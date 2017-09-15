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
    let uu____471 = FStar_Syntax_Print.term_to_string w in
    let uu____472 = FStar_Syntax_Print.term_to_string t in
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
                  let uu____655 = FStar_Syntax_Print.term_to_string g.witness in
                  FStar_Util.JsonStr uu____655 in
                ("witness", uu____654) in
              let uu____656 =
                let uu____663 =
                  let uu____668 =
                    let uu____669 =
                      FStar_Syntax_Print.term_to_string g.goal_ty in
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
let solve: goal -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____1075 = trysolve goal solution in
      if uu____1075
      then ()
      else
        (let uu____1077 =
           let uu____1078 =
             let uu____1079 = FStar_Syntax_Print.term_to_string solution in
             let uu____1080 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____1081 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____1079
               uu____1080 uu____1081 in
           TacFailure uu____1078 in
         FStar_Exn.raise uu____1077)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____1087 =
         let uu___88_1088 = p in
         let uu____1089 = FStar_List.tl p.goals in
         {
           main_context = (uu___88_1088.main_context);
           main_goal = (uu___88_1088.main_goal);
           all_implicits = (uu___88_1088.all_implicits);
           goals = uu____1089;
           smt_goals = (uu___88_1088.smt_goals)
         } in
       set uu____1087)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___89_1098 = p in
          {
            main_context = (uu___89_1098.main_context);
            main_goal = (uu___89_1098.main_goal);
            all_implicits = (uu___89_1098.all_implicits);
            goals = [];
            smt_goals = (uu___89_1098.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___90_1115 = p in
            {
              main_context = (uu___90_1115.main_context);
              main_goal = (uu___90_1115.main_goal);
              all_implicits = (uu___90_1115.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___90_1115.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___91_1132 = p in
            {
              main_context = (uu___91_1132.main_context);
              main_goal = (uu___91_1132.main_goal);
              all_implicits = (uu___91_1132.all_implicits);
              goals = (uu___91_1132.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___92_1149 = p in
            {
              main_context = (uu___92_1149.main_context);
              main_goal = (uu___92_1149.main_goal);
              all_implicits = (uu___92_1149.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___92_1149.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___93_1166 = p in
            {
              main_context = (uu___93_1166.main_context);
              main_goal = (uu___93_1166.main_goal);
              all_implicits = (uu___93_1166.all_implicits);
              goals = (uu___93_1166.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1176  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___94_1189 = p in
            {
              main_context = (uu___94_1189.main_context);
              main_goal = (uu___94_1189.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___94_1189.goals);
              smt_goals = (uu___94_1189.smt_goals)
            }))
let new_uvar: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun typ  ->
      let uu____1214 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____1214 with
      | (u,uu____1230,g_u) ->
          let uu____1244 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____1244 (fun uu____1248  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1253 = FStar_Syntax_Util.un_squash t in
    match uu____1253 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1263 =
          let uu____1264 = FStar_Syntax_Subst.compress t' in
          uu____1264.FStar_Syntax_Syntax.n in
        (match uu____1263 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1268 -> false)
    | uu____1269 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1278 = FStar_Syntax_Util.un_squash t in
    match uu____1278 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1288 =
          let uu____1289 = FStar_Syntax_Subst.compress t' in
          uu____1289.FStar_Syntax_Syntax.n in
        (match uu____1288 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1293 -> false)
    | uu____1294 -> false
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
        let uu____1328 = new_uvar env typ in
        bind uu____1328
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
        let uu____1351 = mk_irrelevant_goal env phi opts in
        bind uu____1351 (fun goal  -> add_goals [goal])
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
       let uu____1374 = istrivial goal.context goal.goal_ty in
       if uu____1374
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____1379 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1379))
let add_goal_from_guard:
  env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Options.optionstate -> Prims.unit tac
  =
  fun e  ->
    fun g  ->
      fun opts  ->
        let uu____1396 =
          let uu____1397 = FStar_TypeChecker_Rel.simplify_guard e g in
          uu____1397.FStar_TypeChecker_Env.guard_f in
        match uu____1396 with
        | FStar_TypeChecker_Common.Trivial  -> ret ()
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____1401 = istrivial e f in
            if uu____1401
            then ret ()
            else
              (let uu____1405 = mk_irrelevant_goal e f opts in
               bind uu____1405
                 (fun goal  ->
                    let goal1 =
                      let uu___95_1412 = goal in
                      {
                        context = (uu___95_1412.context);
                        witness = (uu___95_1412.witness);
                        goal_ty = (uu___95_1412.goal_ty);
                        opts = (uu___95_1412.opts);
                        is_guard = true
                      } in
                    push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1418 = is_irrelevant g in
       if uu____1418
       then bind dismiss (fun uu____1422  -> add_smt_goals [g])
       else
         (let uu____1424 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1424))
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
             let uu____1470 =
               try
                 let uu____1504 = FStar_List.splitAt n1 p.goals in
                 ret uu____1504
               with | uu____1534 -> fail "divide: not enough goals" in
             bind uu____1470
               (fun uu____1561  ->
                  match uu____1561 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___96_1587 = p in
                        {
                          main_context = (uu___96_1587.main_context);
                          main_goal = (uu___96_1587.main_goal);
                          all_implicits = (uu___96_1587.all_implicits);
                          goals = lgs;
                          smt_goals = []
                        } in
                      let rp =
                        let uu___97_1589 = p in
                        {
                          main_context = (uu___97_1589.main_context);
                          main_goal = (uu___97_1589.main_goal);
                          all_implicits = (uu___97_1589.all_implicits);
                          goals = rgs;
                          smt_goals = []
                        } in
                      let uu____1590 = set lp in
                      bind uu____1590
                        (fun uu____1598  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1612 = set rp in
                                     bind uu____1612
                                       (fun uu____1620  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___98_1636 = p in
                                                      {
                                                        main_context =
                                                          (uu___98_1636.main_context);
                                                        main_goal =
                                                          (uu___98_1636.main_goal);
                                                        all_implicits =
                                                          (uu___98_1636.all_implicits);
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
                                                    let uu____1637 = set p' in
                                                    bind uu____1637
                                                      (fun uu____1645  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1665 = divide (Prims.parse_int "1") f idtac in
    bind uu____1665
      (fun uu____1678  -> match uu____1678 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.goals with
         | [] -> ret []
         | uu____1713::uu____1714 ->
             let uu____1717 =
               let uu____1726 = map tau in
               divide (Prims.parse_int "1") tau uu____1726 in
             bind uu____1717
               (fun uu____1744  ->
                  match uu____1744 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1783 =
        bind t1
          (fun uu____1788  ->
             let uu____1789 = map t2 in
             bind uu____1789 (fun uu____1797  -> ret ())) in
      focus uu____1783
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1808 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1808 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1823 =
             let uu____1824 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1824 in
           if uu____1823
           then fail "Codomain is effectful"
           else
             (let env' = FStar_TypeChecker_Env.push_binders goal.context [b] in
              let typ' = comp_to_typ c in
              let uu____1830 = new_uvar env' typ' in
              bind uu____1830
                (fun u  ->
                   let uu____1837 =
                     let uu____1838 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1838 in
                   if uu____1837
                   then
                     let uu____1841 =
                       let uu____1844 =
                         let uu___101_1845 = goal in
                         let uu____1846 = bnorm env' u in
                         let uu____1847 = bnorm env' typ' in
                         {
                           context = env';
                           witness = uu____1846;
                           goal_ty = uu____1847;
                           opts = (uu___101_1845.opts);
                           is_guard = (uu___101_1845.is_guard)
                         } in
                       replace_cur uu____1844 in
                     bind uu____1841 (fun uu____1849  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1855 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1855)
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
       (let uu____1876 = FStar_Syntax_Util.arrow_one goal.goal_ty in
        match uu____1876 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1895 =
              let uu____1896 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1896 in
            if uu____1895
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None goal.goal_ty in
               let bs =
                 let uu____1912 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1912; b] in
               let env' = FStar_TypeChecker_Env.push_binders goal.context bs in
               let uu____1914 =
                 let uu____1917 = comp_to_typ c in new_uvar env' uu____1917 in
               bind uu____1914
                 (fun u  ->
                    let lb =
                      let uu____1933 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.goal_ty FStar_Parser_Const.effect_Tot_lid
                        uu____1933 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1937 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1937 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____1974 =
                            let uu____1977 =
                              let uu___102_1978 = goal in
                              let uu____1979 = bnorm env' u in
                              let uu____1980 =
                                let uu____1981 = comp_to_typ c in
                                bnorm env' uu____1981 in
                              {
                                context = env';
                                witness = uu____1979;
                                goal_ty = uu____1980;
                                opts = (uu___102_1978.opts);
                                is_guard = (uu___102_1978.is_guard)
                              } in
                            replace_cur uu____1977 in
                          bind uu____1974
                            (fun uu____1988  ->
                               let uu____1989 =
                                 let uu____1994 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____1994, b) in
                               ret uu____1989)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2008 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2008))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2033 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2033 in
         let w = normalize steps goal.context goal.witness in
         let t = normalize steps goal.context goal.goal_ty in
         replace_cur
           (let uu___103_2040 = goal in
            {
              context = (uu___103_2040.context);
              witness = w;
              goal_ty = t;
              opts = (uu___103_2040.opts);
              is_guard = (uu___103_2040.is_guard)
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
             let uu____2064 = FStar_TypeChecker_Normalize.tr_norm_steps s in
             FStar_List.append
               [FStar_TypeChecker_Normalize.Reify;
               FStar_TypeChecker_Normalize.UnfoldTac] uu____2064 in
           let t1 = normalize steps ps.main_context t in ret t1)
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2079 =
           try
             let uu____2107 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____2107
           with
           | e ->
               let uu____2134 = FStar_Syntax_Print.term_to_string t in
               let uu____2135 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____2134
                 uu____2135 in
         bind uu____2079
           (fun uu____2153  ->
              match uu____2153 with
              | (t1,typ,guard) ->
                  let uu____2165 =
                    let uu____2166 =
                      let uu____2167 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2167 in
                    Prims.op_Negation uu____2166 in
                  if uu____2165
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2171 = do_unify goal.context typ goal.goal_ty in
                     if uu____2171
                     then (solve goal t1; dismiss)
                     else
                       (let uu____2176 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____2177 =
                          let uu____2178 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____2178 in
                        let uu____2179 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2176 uu____2177 uu____2179))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  -> let uu____2188 = __exact t in focus uu____2188
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2202 =
           try
             let uu____2230 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____2230
           with
           | e ->
               let uu____2257 = FStar_Syntax_Print.term_to_string t in
               let uu____2258 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2257
                 uu____2258 in
         bind uu____2202
           (fun uu____2276  ->
              match uu____2276 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2294 =
                       let uu____2295 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2295 in
                     if uu____2294
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2299 =
                          let uu____2308 =
                            let uu____2317 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2317.FStar_Syntax_Syntax.effect_args in
                          match uu____2308 with
                          | pre::post::uu____2328 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2369 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2299 with
                        | (pre,post) ->
                            let uu____2398 =
                              do_unify goal.context post goal.goal_ty in
                            if uu____2398
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____2403  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____2405 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____2406 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____2407 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2405 uu____2406 uu____2407)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.is_guard
      then false
      else
        (let free_uvars =
           let uu____2420 =
             let uu____2427 = FStar_Syntax_Free.uvars g.goal_ty in
             FStar_Util.set_elements uu____2427 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2420 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2454 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2474 =
               let uu____2479 = __exact tm in trytac uu____2479 in
             bind uu____2474
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2492 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2492 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           let uu____2522 =
                             let uu____2523 =
                               FStar_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu____2523 in
                           if uu____2522
                           then fail "apply: not total codomain"
                           else
                             (let uu____2527 =
                                new_uvar goal.context
                                  bv.FStar_Syntax_Syntax.sort in
                              bind uu____2527
                                (fun u  ->
                                   let tm' =
                                     FStar_Syntax_Syntax.mk_Tm_app tm
                                       [(u, aq)] FStar_Pervasives_Native.None
                                       (goal.context).FStar_TypeChecker_Env.range in
                                   let typ' =
                                     let uu____2547 = comp_to_typ c in
                                     FStar_All.pipe_left
                                       (FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.NT (bv, u)])
                                       uu____2547 in
                                   let uu____2548 = __apply uopt tm' typ' in
                                   bind uu____2548
                                     (fun uu____2555  ->
                                        let uu____2556 =
                                          let uu____2557 =
                                            let uu____2560 =
                                              let uu____2561 =
                                                FStar_Syntax_Util.head_and_args
                                                  u in
                                              FStar_Pervasives_Native.fst
                                                uu____2561 in
                                            FStar_Syntax_Subst.compress
                                              uu____2560 in
                                          uu____2557.FStar_Syntax_Syntax.n in
                                        match uu____2556 with
                                        | FStar_Syntax_Syntax.Tm_uvar
                                            (uvar,uu____2589) ->
                                            bind get
                                              (fun ps  ->
                                                 let uu____2617 =
                                                   uopt &&
                                                     (uvar_free uvar ps) in
                                                 if uu____2617
                                                 then ret ()
                                                 else
                                                   (let uu____2621 =
                                                      let uu____2624 =
                                                        let uu___108_2625 =
                                                          goal in
                                                        let uu____2626 =
                                                          bnorm goal.context
                                                            u in
                                                        let uu____2627 =
                                                          bnorm goal.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          context =
                                                            (uu___108_2625.context);
                                                          witness =
                                                            uu____2626;
                                                          goal_ty =
                                                            uu____2627;
                                                          opts =
                                                            (uu___108_2625.opts);
                                                          is_guard = false
                                                        } in
                                                      [uu____2624] in
                                                    add_goals uu____2621))
                                        | uu____2628 -> ret ()))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2686 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____2686 with
           | (tm1,typ,guard) ->
               let uu____2698 =
                 let uu____2701 =
                   let uu____2704 = __apply uopt tm1 typ in
                   bind uu____2704
                     (fun uu____2708  ->
                        add_goal_from_guard goal.context guard goal.opts) in
                 focus uu____2701 in
               let uu____2709 =
                 let uu____2712 = FStar_Syntax_Print.term_to_string tm1 in
                 let uu____2713 = FStar_Syntax_Print.term_to_string typ in
                 let uu____2714 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 fail3
                   "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                   uu____2712 uu____2713 uu____2714 in
               try_unif uu____2698 uu____2709)
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2723 =
      let is_unit_t t =
        let uu____2730 =
          let uu____2731 = FStar_Syntax_Subst.compress t in
          uu____2731.FStar_Syntax_Syntax.n in
        match uu____2730 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
            true
        | uu____2735 -> false in
      bind cur_goal
        (fun goal  ->
           let uu____2745 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____2745 with
           | (tm1,t,guard) ->
               let uu____2757 = FStar_Syntax_Util.arrow_formals_comp t in
               (match uu____2757 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2787 =
                         FStar_List.fold_left
                           (fun uu____2833  ->
                              fun uu____2834  ->
                                match (uu____2833, uu____2834) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2937 = is_unit_t b_t in
                                    if uu____2937
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____2975 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.context b_t in
                                       match uu____2975 with
                                       | (u,uu____3005,g_u) ->
                                           let uu____3019 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____3019,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2787 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____3089 =
                             let uu____3098 =
                               let uu____3107 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____3107.FStar_Syntax_Syntax.effect_args in
                             match uu____3098 with
                             | pre::post::uu____3118 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____3159 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____3089 with
                            | (pre,post) ->
                                let uu____3188 =
                                  let uu____3189 =
                                    let uu____3190 =
                                      FStar_Syntax_Util.mk_squash post in
                                    do_unify goal.context uu____3190
                                      goal.goal_ty in
                                  Prims.op_Negation uu____3189 in
                                if uu____3188
                                then
                                  let uu____3193 =
                                    FStar_Syntax_Print.term_to_string tm1 in
                                  let uu____3194 =
                                    let uu____3195 =
                                      FStar_Syntax_Util.mk_squash post in
                                    FStar_Syntax_Print.term_to_string
                                      uu____3195 in
                                  let uu____3196 =
                                    FStar_Syntax_Print.term_to_string
                                      goal.goal_ty in
                                  fail3
                                    "apply_lemma: Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                    uu____3193 uu____3194 uu____3196
                                else
                                  (let solution =
                                     FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                       FStar_Pervasives_Native.None
                                       (goal.context).FStar_TypeChecker_Env.range in
                                   let implicits1 =
                                     FStar_All.pipe_right
                                       implicits.FStar_TypeChecker_Env.implicits
                                       (FStar_List.filter
                                          (fun uu____3268  ->
                                             match uu____3268 with
                                             | (uu____3281,uu____3282,uu____3283,tm2,uu____3285,uu____3286)
                                                 ->
                                                 let uu____3287 =
                                                   FStar_Syntax_Util.head_and_args
                                                     tm2 in
                                                 (match uu____3287 with
                                                  | (hd1,uu____3303) ->
                                                      let uu____3324 =
                                                        let uu____3325 =
                                                          FStar_Syntax_Subst.compress
                                                            hd1 in
                                                        uu____3325.FStar_Syntax_Syntax.n in
                                                      (match uu____3324 with
                                                       | FStar_Syntax_Syntax.Tm_uvar
                                                           uu____3328 -> true
                                                       | uu____3345 -> false)))) in
                                   solve goal solution;
                                   (let uu____3347 = add_implicits implicits1 in
                                    bind uu____3347
                                      (fun uu____3351  ->
                                         bind dismiss
                                           (fun uu____3360  ->
                                              let is_free_uvar uv t1 =
                                                let free_uvars =
                                                  let uu____3371 =
                                                    let uu____3378 =
                                                      FStar_Syntax_Free.uvars
                                                        t1 in
                                                    FStar_Util.set_elements
                                                      uu____3378 in
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.fst
                                                    uu____3371 in
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
                                                let uu____3419 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t1 in
                                                match uu____3419 with
                                                | (hd1,uu____3435) ->
                                                    (match hd1.FStar_Syntax_Syntax.n
                                                     with
                                                     | FStar_Syntax_Syntax.Tm_uvar
                                                         (uv,uu____3457) ->
                                                         appears uv goals
                                                     | uu____3482 -> false) in
                                              let sub_goals =
                                                FStar_All.pipe_right
                                                  implicits1
                                                  (FStar_List.map
                                                     (fun uu____3524  ->
                                                        match uu____3524 with
                                                        | (_msg,_env,_uvar,term,typ,uu____3542)
                                                            ->
                                                            let uu___111_3543
                                                              = goal in
                                                            let uu____3544 =
                                                              bnorm
                                                                goal.context
                                                                term in
                                                            let uu____3545 =
                                                              bnorm
                                                                goal.context
                                                                typ in
                                                            {
                                                              context =
                                                                (uu___111_3543.context);
                                                              witness =
                                                                uu____3544;
                                                              goal_ty =
                                                                uu____3545;
                                                              opts =
                                                                (uu___111_3543.opts);
                                                              is_guard =
                                                                (uu___111_3543.is_guard)
                                                            })) in
                                              let rec filter' f xs =
                                                match xs with
                                                | [] -> []
                                                | x::xs1 ->
                                                    let uu____3583 = f x xs1 in
                                                    if uu____3583
                                                    then
                                                      let uu____3586 =
                                                        filter' f xs1 in
                                                      x :: uu____3586
                                                    else filter' f xs1 in
                                              let sub_goals1 =
                                                filter'
                                                  (fun g  ->
                                                     fun goals  ->
                                                       let uu____3600 =
                                                         checkone g.witness
                                                           goals in
                                                       Prims.op_Negation
                                                         uu____3600)
                                                  sub_goals in
                                              let uu____3601 =
                                                add_goal_from_guard
                                                  goal.context guard
                                                  goal.opts in
                                              bind uu____3601
                                                (fun uu____3606  ->
                                                   let uu____3607 =
                                                     let uu____3610 =
                                                       let uu____3611 =
                                                         istrivial
                                                           goal.context pre in
                                                       Prims.op_Negation
                                                         uu____3611 in
                                                     if uu____3610
                                                     then
                                                       add_irrelevant_goal
                                                         goal.context pre
                                                         goal.opts
                                                     else ret () in
                                                   bind uu____3607
                                                     (fun uu____3616  ->
                                                        add_goals sub_goals1)))))))))) in
    focus uu____2723
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3633 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3633 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3643::(e1,uu____3645)::(e2,uu____3647)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3706 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3729 = destruct_eq' typ in
    match uu____3729 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3759 = FStar_Syntax_Util.un_squash typ in
        (match uu____3759 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3792 =
           FStar_All.pipe_left mlog
             (fun uu____3802  ->
                let uu____3803 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3804 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3803
                  uu____3804) in
         bind uu____3792
           (fun uu____3812  ->
              let uu____3813 =
                let uu____3820 =
                  let uu____3821 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3821 in
                destruct_eq uu____3820 in
              match uu____3813 with
              | FStar_Pervasives_Native.Some (x,e) ->
                  let uu____3838 =
                    let uu____3839 = FStar_Syntax_Subst.compress x in
                    uu____3839.FStar_Syntax_Syntax.n in
                  (match uu____3838 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___112_3846 = goal in
                         let uu____3847 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____3848 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___112_3846.context);
                           witness = uu____3847;
                           goal_ty = uu____3848;
                           opts = (uu___112_3846.opts);
                           is_guard = (uu___112_3846.is_guard)
                         } in
                       replace_cur goal1
                   | uu____3849 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3850 -> fail "Not an equality hypothesis"))
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
            let uu____3881 = FStar_TypeChecker_Env.pop_bv e in
            match uu____3881 with
            | FStar_Pervasives_Native.None  -> e
            | FStar_Pervasives_Native.Some (bv,e') ->
                if FStar_Syntax_Syntax.bv_eq bv b1
                then FStar_TypeChecker_Env.push_bv e' b2
                else
                  (let uu____3899 = alpha e' in
                   let uu____3900 =
                     let uu___113_3901 = bv in
                     let uu____3902 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___113_3901.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___113_3901.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3902
                     } in
                   FStar_TypeChecker_Env.push_bv uu____3899 uu____3900) in
          let c = alpha g.context in
          let w = FStar_Syntax_Subst.subst s g.witness in
          let t = FStar_Syntax_Subst.subst s g.goal_ty in
          let uu___114_3908 = g in
          {
            context = c;
            witness = w;
            goal_ty = t;
            opts = (uu___114_3908.opts);
            is_guard = (uu___114_3908.is_guard)
          }
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3929 = b in
           match uu____3929 with
           | (bv,uu____3933) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___115_3937 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___115_3937.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___115_3937.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3941 =
                   let uu____3942 =
                     let uu____3949 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3949) in
                   FStar_Syntax_Syntax.NT uu____3942 in
                 [uu____3941] in
               let uu____3950 = subst_goal bv bv' s1 goal in
               replace_cur uu____3950)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3956 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3956 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____3978 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____3978 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___116_4012 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___116_4012.opts);
                is_guard = (uu___116_4012.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4024 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____4024 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4045 = FStar_Syntax_Print.bv_to_string x in
               let uu____4046 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4045 uu____4046
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4053 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____4053 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let uu____4075 = FStar_Util.set_mem x fns_ty in
           if uu____4075
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4079 = new_uvar env' goal.goal_ty in
              bind uu____4079
                (fun u  ->
                   let uu____4085 =
                     let uu____4086 = trysolve goal u in
                     Prims.op_Negation uu____4086 in
                   if uu____4085
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___117_4091 = goal in
                        let uu____4092 = bnorm env' u in
                        {
                          context = env';
                          witness = uu____4092;
                          goal_ty = (uu___117_4091.goal_ty);
                          opts = (uu___117_4091.opts);
                          is_guard = (uu___117_4091.is_guard)
                        } in
                      bind dismiss (fun uu____4094  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4106 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____4106 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4130  ->
                    let uu____4131 = clear b in
                    bind uu____4131
                      (fun uu____4135  ->
                         bind intro (fun uu____4137  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___118_4154 = g in
           {
             context = ctx';
             witness = (uu___118_4154.witness);
             goal_ty = (uu___118_4154.goal_ty);
             opts = (uu___118_4154.opts);
             is_guard = (uu___118_4154.is_guard)
           } in
         bind dismiss (fun uu____4156  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___119_4173 = g in
           {
             context = ctx';
             witness = (uu___119_4173.witness);
             goal_ty = (uu___119_4173.goal_ty);
             opts = (uu___119_4173.opts);
             is_guard = (uu___119_4173.is_guard)
           } in
         bind dismiss (fun uu____4175  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4217 = f x in
          bind uu____4217
            (fun y  ->
               let uu____4225 = mapM f xs in
               bind uu____4225 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4271 = FStar_Syntax_Subst.compress t in
          uu____4271.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4306 = ff hd1 in
              bind uu____4306
                (fun hd2  ->
                   let fa uu____4326 =
                     match uu____4326 with
                     | (a,q) ->
                         let uu____4339 = ff a in
                         bind uu____4339 (fun a1  -> ret (a1, q)) in
                   let uu____4352 = mapM fa args in
                   bind uu____4352
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4412 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4412 with
               | (bs1,t') ->
                   let uu____4421 =
                     let uu____4424 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4424 t' in
                   bind uu____4421
                     (fun t''  ->
                        let uu____4428 =
                          let uu____4429 =
                            let uu____4446 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4447 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4446, uu____4447, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4429 in
                        ret uu____4428))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4468 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___120_4472 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___120_4472.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___120_4472.FStar_Syntax_Syntax.vars)
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
            let uu____4501 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4501 with
            | (t1,lcomp,g) ->
                let uu____4513 =
                  let uu____4514 = FStar_TypeChecker_Rel.is_trivial g in
                  Prims.op_Negation uu____4514 in
                if uu____4513
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4521 = new_uvar env typ in
                   bind uu____4521
                     (fun ut  ->
                        log ps
                          (fun uu____4532  ->
                             let uu____4533 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4534 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4533 uu____4534);
                        (let uu____4535 =
                           let uu____4538 =
                             let uu____4539 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4539 typ t1 ut in
                           add_irrelevant_goal env uu____4538 opts in
                         bind uu____4535
                           (fun uu____4542  ->
                              let uu____4543 =
                                bind tau
                                  (fun uu____4548  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4543))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4569 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4569 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____4606  ->
                   let uu____4607 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4607);
              bind dismiss_all
                (fun uu____4610  ->
                   let uu____4611 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____4611
                     (fun gt'  ->
                        log ps
                          (fun uu____4621  ->
                             let uu____4622 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4622);
                        (let uu____4623 = push_goals gs in
                         bind uu____4623
                           (fun uu____4627  ->
                              add_goals
                                [(let uu___121_4629 = g in
                                  {
                                    context = (uu___121_4629.context);
                                    witness = (uu___121_4629.witness);
                                    goal_ty = gt';
                                    opts = (uu___121_4629.opts);
                                    is_guard = (uu___121_4629.is_guard)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4649 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____4649 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4661 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4661 with
            | (hd1,args) ->
                let uu____4694 =
                  let uu____4707 =
                    let uu____4708 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4708.FStar_Syntax_Syntax.n in
                  (uu____4707, args) in
                (match uu____4694 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4722::(l,uu____4724)::(r,uu____4726)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4773 =
                       let uu____4774 = do_unify g.context l r in
                       Prims.op_Negation uu____4774 in
                     if uu____4773
                     then
                       let uu____4777 = FStar_Syntax_Print.term_to_string l in
                       let uu____4778 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4777 uu____4778
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____4782) ->
                     let uu____4799 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____4799))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4807 = new_uvar g.context g.goal_ty in
       bind uu____4807
         (fun u  ->
            let g' =
              let uu___122_4814 = g in
              {
                context = (uu___122_4814.context);
                witness = u;
                goal_ty = (uu___122_4814.goal_ty);
                opts = (uu___122_4814.opts);
                is_guard = (uu___122_4814.is_guard)
              } in
            bind dismiss
              (fun uu____4817  ->
                 let uu____4818 =
                   let uu____4821 =
                     let uu____4822 =
                       FStar_TypeChecker_TcTerm.universe_of g.context
                         g.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4822 g.goal_ty u
                       g.witness in
                   add_irrelevant_goal g.context uu____4821 g.opts in
                 bind uu____4818
                   (fun uu____4825  ->
                      let uu____4826 = add_goals [g'] in
                      bind uu____4826 (fun uu____4830  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___123_4847 = ps in
              {
                main_context = (uu___123_4847.main_context);
                main_goal = (uu___123_4847.main_goal);
                all_implicits = (uu___123_4847.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___123_4847.smt_goals)
              })
       | uu____4848 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___124_4863 = ps in
              {
                main_context = (uu___124_4863.main_context);
                main_goal = (uu___124_4863.main_goal);
                all_implicits = (uu___124_4863.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___124_4863.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____4870 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____4912 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____4912 with
         | (t1,typ,guard) ->
             let uu____4928 = FStar_Syntax_Util.head_and_args typ in
             (match uu____4928 with
              | (hd1,args) ->
                  let uu____4971 =
                    let uu____4984 =
                      let uu____4985 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____4985.FStar_Syntax_Syntax.n in
                    (uu____4984, args) in
                  (match uu____4971 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____5004)::(q,uu____5006)::[]) when
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
                         let uu___125_5044 = g in
                         let uu____5045 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____5045;
                           witness = (uu___125_5044.witness);
                           goal_ty = (uu___125_5044.goal_ty);
                           opts = (uu___125_5044.opts);
                           is_guard = (uu___125_5044.is_guard)
                         } in
                       let g2 =
                         let uu___126_5047 = g in
                         let uu____5048 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____5048;
                           witness = (uu___126_5047.witness);
                           goal_ty = (uu___126_5047.goal_ty);
                           opts = (uu___126_5047.opts);
                           is_guard = (uu___126_5047.is_guard)
                         } in
                       bind dismiss
                         (fun uu____5055  ->
                            let uu____5056 = add_goals [g1; g2] in
                            bind uu____5056
                              (fun uu____5065  ->
                                 let uu____5066 =
                                   let uu____5071 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____5072 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____5071, uu____5072) in
                                 ret uu____5066))
                   | uu____5077 ->
                       let uu____5090 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____5090)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5113 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____5113);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___127_5120 = g in
                 {
                   context = (uu___127_5120.context);
                   witness = (uu___127_5120.witness);
                   goal_ty = (uu___127_5120.goal_ty);
                   opts = opts';
                   is_guard = (uu___127_5120.is_guard)
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
           let uu____5161 =
             (goal.context).FStar_TypeChecker_Env.type_of env tm in
           match uu____5161 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5190 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5196 =
              let uu____5197 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5197 in
            new_uvar env uu____5196 in
      bind uu____5190
        (fun typ  ->
           let uu____5209 = new_uvar env typ in
           bind uu____5209 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5229 = do_unify ps.main_context t1 t2 in ret uu____5229)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5249  ->
             let uu____5250 = FStar_Options.unsafe_tactic_exec () in
             if uu____5250
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5256  -> fun uu____5257  -> false) in
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
      let uu____5279 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5279 with
      | (u,uu____5297,g_u) ->
          let g =
            let uu____5312 = FStar_Options.peek () in
            {
              context = env;
              witness = u;
              goal_ty = typ;
              opts = uu____5312;
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
      let uu____5329 = goal_of_goal_ty env typ in
      match uu____5329 with
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