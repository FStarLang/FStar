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
         let uu___90_1073 = p in
         let uu____1074 = FStar_List.tl p.goals in
         {
           main_context = (uu___90_1073.main_context);
           main_goal = (uu___90_1073.main_goal);
           all_implicits = (uu___90_1073.all_implicits);
           goals = uu____1074;
           smt_goals = (uu___90_1073.smt_goals)
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
         (let uu___91_1103 = p in
          {
            main_context = (uu___91_1103.main_context);
            main_goal = (uu___91_1103.main_goal);
            all_implicits = (uu___91_1103.all_implicits);
            goals = [];
            smt_goals = (uu___91_1103.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___92_1120 = p in
            {
              main_context = (uu___92_1120.main_context);
              main_goal = (uu___92_1120.main_goal);
              all_implicits = (uu___92_1120.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___92_1120.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___93_1137 = p in
            {
              main_context = (uu___93_1137.main_context);
              main_goal = (uu___93_1137.main_goal);
              all_implicits = (uu___93_1137.all_implicits);
              goals = (uu___93_1137.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___94_1154 = p in
            {
              main_context = (uu___94_1154.main_context);
              main_goal = (uu___94_1154.main_goal);
              all_implicits = (uu___94_1154.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___94_1154.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___95_1171 = p in
            {
              main_context = (uu___95_1171.main_context);
              main_goal = (uu___95_1171.main_goal);
              all_implicits = (uu___95_1171.all_implicits);
              goals = (uu___95_1171.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1181  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___96_1194 = p in
            {
              main_context = (uu___96_1194.main_context);
              main_goal = (uu___96_1194.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___96_1194.goals);
              smt_goals = (uu___96_1194.smt_goals)
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
                      let uu___97_1415 = goal in
                      {
                        context = (uu___97_1415.context);
                        witness = (uu___97_1415.witness);
                        goal_ty = (uu___97_1415.goal_ty);
                        opts = (uu___97_1415.opts);
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
                        let uu___98_1590 = p in
                        {
                          main_context = (uu___98_1590.main_context);
                          main_goal = (uu___98_1590.main_goal);
                          all_implicits = (uu___98_1590.all_implicits);
                          goals = lgs;
                          smt_goals = []
                        } in
                      let rp =
                        let uu___99_1592 = p in
                        {
                          main_context = (uu___99_1592.main_context);
                          main_goal = (uu___99_1592.main_goal);
                          all_implicits = (uu___99_1592.all_implicits);
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
                                                      let uu___100_1639 = p in
                                                      {
                                                        main_context =
                                                          (uu___100_1639.main_context);
                                                        main_goal =
                                                          (uu___100_1639.main_goal);
                                                        all_implicits =
                                                          (uu___100_1639.all_implicits);
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
                         let uu___103_1848 = goal in
                         let uu____1849 = bnorm env' u in
                         let uu____1850 = bnorm env' typ' in
                         {
                           context = env';
                           witness = uu____1849;
                           goal_ty = uu____1850;
                           opts = (uu___103_1848.opts);
                           is_guard = (uu___103_1848.is_guard)
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
                              let uu___104_1981 = goal in
                              let uu____1982 = bnorm env' u in
                              let uu____1983 =
                                let uu____1984 = comp_to_typ c in
                                bnorm env' uu____1984 in
                              {
                                context = env';
                                witness = uu____1982;
                                goal_ty = uu____1983;
                                opts = (uu___104_1981.opts);
                                is_guard = (uu___104_1981.is_guard)
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
           (let uu___105_2043 = goal in
            {
              context = (uu___105_2043.context);
              witness = w;
              goal_ty = t;
              opts = (uu___105_2043.opts);
              is_guard = (uu___105_2043.is_guard)
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
                                                        let uu___110_2631 =
                                                          goal in
                                                        let uu____2632 =
                                                          bnorm goal.context
                                                            u1 in
                                                        let uu____2633 =
                                                          bnorm goal.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          context =
                                                            (uu___110_2631.context);
                                                          witness =
                                                            uu____2632;
                                                          goal_ty =
                                                            uu____2633;
                                                          opts =
                                                            (uu___110_2631.opts);
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
                                     let uu____3207 =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       goal.context uu____3207 in
                                   let implicits1 =
                                     FStar_All.pipe_right
                                       implicits.FStar_TypeChecker_Env.implicits
                                       (FStar_List.filter
                                          (fun uu____3275  ->
                                             match uu____3275 with
                                             | (uu____3288,uu____3289,uu____3290,tm2,uu____3292,uu____3293)
                                                 ->
                                                 let uu____3294 =
                                                   FStar_Syntax_Util.head_and_args
                                                     tm2 in
                                                 (match uu____3294 with
                                                  | (hd1,uu____3310) ->
                                                      let uu____3331 =
                                                        let uu____3332 =
                                                          FStar_Syntax_Subst.compress
                                                            hd1 in
                                                        uu____3332.FStar_Syntax_Syntax.n in
                                                      (match uu____3331 with
                                                       | FStar_Syntax_Syntax.Tm_uvar
                                                           uu____3335 -> true
                                                       | uu____3352 -> false)))) in
                                   let uu____3353 = solve goal solution in
                                   bind uu____3353
                                     (fun uu____3358  ->
                                        let uu____3359 =
                                          add_implicits implicits1 in
                                        bind uu____3359
                                          (fun uu____3370  ->
                                             let is_free_uvar uv t1 =
                                               let free_uvars =
                                                 let uu____3381 =
                                                   let uu____3388 =
                                                     FStar_Syntax_Free.uvars
                                                       t1 in
                                                   FStar_Util.set_elements
                                                     uu____3388 in
                                                 FStar_List.map
                                                   FStar_Pervasives_Native.fst
                                                   uu____3381 in
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
                                               let uu____3429 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t1 in
                                               match uu____3429 with
                                               | (hd1,uu____3445) ->
                                                   (match hd1.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_uvar
                                                        (uv,uu____3467) ->
                                                        appears uv goals
                                                    | uu____3492 -> false) in
                                             let sub_goals =
                                               FStar_All.pipe_right
                                                 implicits1
                                                 (FStar_List.map
                                                    (fun uu____3534  ->
                                                       match uu____3534 with
                                                       | (_msg,_env,_uvar,term,typ,uu____3552)
                                                           ->
                                                           let uu___113_3553
                                                             = goal in
                                                           let uu____3554 =
                                                             bnorm
                                                               goal.context
                                                               term in
                                                           let uu____3555 =
                                                             bnorm
                                                               goal.context
                                                               typ in
                                                           {
                                                             context =
                                                               (uu___113_3553.context);
                                                             witness =
                                                               uu____3554;
                                                             goal_ty =
                                                               uu____3555;
                                                             opts =
                                                               (uu___113_3553.opts);
                                                             is_guard =
                                                               (uu___113_3553.is_guard)
                                                           })) in
                                             let rec filter' f xs =
                                               match xs with
                                               | [] -> []
                                               | x::xs1 ->
                                                   let uu____3593 = f x xs1 in
                                                   if uu____3593
                                                   then
                                                     let uu____3596 =
                                                       filter' f xs1 in
                                                     x :: uu____3596
                                                   else filter' f xs1 in
                                             let sub_goals1 =
                                               filter'
                                                 (fun g  ->
                                                    fun goals  ->
                                                      let uu____3610 =
                                                        checkone g.witness
                                                          goals in
                                                      Prims.op_Negation
                                                        uu____3610) sub_goals in
                                             let uu____3611 =
                                               add_goal_from_guard
                                                 goal.context guard goal.opts in
                                             bind uu____3611
                                               (fun uu____3616  ->
                                                  let uu____3617 =
                                                    let uu____3620 =
                                                      let uu____3621 =
                                                        let uu____3622 =
                                                          FStar_Syntax_Util.mk_squash
                                                            pre in
                                                        istrivial
                                                          goal.context
                                                          uu____3622 in
                                                      Prims.op_Negation
                                                        uu____3621 in
                                                    if uu____3620
                                                    then
                                                      add_irrelevant_goal
                                                        goal.context pre
                                                        goal.opts
                                                    else ret () in
                                                  bind uu____3617
                                                    (fun uu____3627  ->
                                                       add_goals sub_goals1))))))))) in
    focus uu____2731
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3644 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3644 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3654::(e1,uu____3656)::(e2,uu____3658)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3717 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3740 = destruct_eq' typ in
    match uu____3740 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3770 = FStar_Syntax_Util.un_squash typ in
        (match uu____3770 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3803 =
           FStar_All.pipe_left mlog
             (fun uu____3813  ->
                let uu____3814 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3815 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3814
                  uu____3815) in
         bind uu____3803
           (fun uu____3823  ->
              let uu____3824 =
                let uu____3831 =
                  let uu____3832 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3832 in
                destruct_eq uu____3831 in
              match uu____3824 with
              | FStar_Pervasives_Native.Some (x,e) ->
                  let uu____3849 =
                    let uu____3850 = FStar_Syntax_Subst.compress x in
                    uu____3850.FStar_Syntax_Syntax.n in
                  (match uu____3849 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___114_3857 = goal in
                         let uu____3858 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____3859 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___114_3857.context);
                           witness = uu____3858;
                           goal_ty = uu____3859;
                           opts = (uu___114_3857.opts);
                           is_guard = (uu___114_3857.is_guard)
                         } in
                       replace_cur goal1
                   | uu____3860 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3861 -> fail "Not an equality hypothesis"))
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
            let uu____3892 = FStar_TypeChecker_Env.pop_bv e in
            match uu____3892 with
            | FStar_Pervasives_Native.None  -> e
            | FStar_Pervasives_Native.Some (bv,e') ->
                if FStar_Syntax_Syntax.bv_eq bv b1
                then FStar_TypeChecker_Env.push_bv e' b2
                else
                  (let uu____3910 = alpha e' in
                   let uu____3911 =
                     let uu___115_3912 = bv in
                     let uu____3913 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___115_3912.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___115_3912.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3913
                     } in
                   FStar_TypeChecker_Env.push_bv uu____3910 uu____3911) in
          let c = alpha g.context in
          let w = FStar_Syntax_Subst.subst s g.witness in
          let t = FStar_Syntax_Subst.subst s g.goal_ty in
          let uu___116_3919 = g in
          {
            context = c;
            witness = w;
            goal_ty = t;
            opts = (uu___116_3919.opts);
            is_guard = (uu___116_3919.is_guard)
          }
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3940 = b in
           match uu____3940 with
           | (bv,uu____3944) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___117_3948 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___117_3948.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___117_3948.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3952 =
                   let uu____3953 =
                     let uu____3960 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3960) in
                   FStar_Syntax_Syntax.NT uu____3953 in
                 [uu____3952] in
               let uu____3961 = subst_goal bv bv' s1 goal in
               replace_cur uu____3961)
let rec find_bv_env:
  env ->
    FStar_Syntax_Syntax.bv ->
      (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.universe,
        env,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple6 tac
  =
  fun e  ->
    fun bv  ->
      let uu____4002 = FStar_TypeChecker_Env.pop_bv e in
      match uu____4002 with
      | FStar_Pervasives_Native.None  ->
          fail "binder_retype: binder is not present in environment"
      | FStar_Pervasives_Native.Some (bv',e') ->
          if FStar_Syntax_Syntax.bv_eq bv bv'
          then
            let uu____4065 =
              let uu____4072 = FStar_Syntax_Util.type_u () in
              match uu____4072 with | (ty,u) -> ret (ty, u) in
            bind uu____4065
              (fun uu____4111  ->
                 match uu____4111 with
                 | (ty,u) ->
                     let uu____4134 = new_uvar e' ty in
                     bind uu____4134
                       (fun t'  ->
                          let bv'' =
                            let uu___118_4156 = bv in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___118_4156.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___118_4156.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t'
                            } in
                          let uu____4157 =
                            let uu____4172 =
                              FStar_TypeChecker_Env.push_bv e' bv'' in
                            let uu____4173 =
                              let uu____4176 =
                                let uu____4177 =
                                  let uu____4184 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4184) in
                                FStar_Syntax_Syntax.NT uu____4177 in
                              [uu____4176] in
                            (e', ty, t', u, uu____4172, uu____4173) in
                          ret uu____4157))
          else
            (let uu____4202 = find_bv_env e' bv in
             bind uu____4202
               (fun uu____4256  ->
                  match uu____4256 with
                  | (e1,ty,t,u,e2,s) ->
                      let bv'1 =
                        let uu___119_4298 = bv' in
                        let uu____4299 =
                          FStar_Syntax_Subst.subst s
                            bv'.FStar_Syntax_Syntax.sort in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___119_4298.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___119_4298.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = uu____4299
                        } in
                      let uu____4302 =
                        let uu____4317 =
                          FStar_TypeChecker_Env.push_bv e2 bv'1 in
                        (e1, ty, t, u, uu____4317, s) in
                      ret uu____4302))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4347 = b in
         match uu____4347 with
         | (bv,uu____4351) ->
             bind dismiss
               (fun uu____4354  ->
                  let uu____4355 = find_bv_env goal.context bv in
                  bind uu____4355
                    (fun uu____4394  ->
                       match uu____4394 with
                       | (env',ty,t',u,env,s) ->
                           let uu____4421 =
                             let uu____4424 =
                               let uu____4427 =
                                 let uu___120_4428 = goal in
                                 let uu____4429 =
                                   FStar_Syntax_Subst.subst s goal.witness in
                                 let uu____4430 =
                                   FStar_Syntax_Subst.subst s goal.goal_ty in
                                 {
                                   context = env;
                                   witness = uu____4429;
                                   goal_ty = uu____4430;
                                   opts = (uu___120_4428.opts);
                                   is_guard = (uu___120_4428.is_guard)
                                 } in
                               [uu____4427] in
                             add_goals uu____4424 in
                           bind uu____4421
                             (fun uu____4433  ->
                                let uu____4434 =
                                  FStar_Syntax_Util.mk_eq2
                                    (FStar_Syntax_Syntax.U_succ u) ty
                                    bv.FStar_Syntax_Syntax.sort t' in
                                add_irrelevant_goal env' uu____4434 goal.opts))))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4440 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____4440 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4462 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4462 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___121_4496 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___121_4496.opts);
                is_guard = (uu___121_4496.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4508 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____4508 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4529 = FStar_Syntax_Print.bv_to_string x in
               let uu____4530 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4529 uu____4530
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4537 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____4537 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let uu____4559 = FStar_Util.set_mem x fns_ty in
           if uu____4559
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4563 = new_uvar env' goal.goal_ty in
              bind uu____4563
                (fun u  ->
                   let uu____4569 =
                     let uu____4570 = trysolve goal u in
                     Prims.op_Negation uu____4570 in
                   if uu____4569
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___122_4575 = goal in
                        let uu____4576 = bnorm env' u in
                        {
                          context = env';
                          witness = uu____4576;
                          goal_ty = (uu___122_4575.goal_ty);
                          opts = (uu___122_4575.opts);
                          is_guard = (uu___122_4575.is_guard)
                        } in
                      bind dismiss (fun uu____4578  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4590 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____4590 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4614  ->
                    let uu____4615 = clear b in
                    bind uu____4615
                      (fun uu____4619  ->
                         bind intro (fun uu____4621  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___123_4638 = g in
           {
             context = ctx';
             witness = (uu___123_4638.witness);
             goal_ty = (uu___123_4638.goal_ty);
             opts = (uu___123_4638.opts);
             is_guard = (uu___123_4638.is_guard)
           } in
         bind dismiss (fun uu____4640  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___124_4657 = g in
           {
             context = ctx';
             witness = (uu___124_4657.witness);
             goal_ty = (uu___124_4657.goal_ty);
             opts = (uu___124_4657.opts);
             is_guard = (uu___124_4657.is_guard)
           } in
         bind dismiss (fun uu____4659  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4701 = f x in
          bind uu____4701
            (fun y  ->
               let uu____4709 = mapM f xs in
               bind uu____4709 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4755 = FStar_Syntax_Subst.compress t in
          uu____4755.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4790 = ff hd1 in
              bind uu____4790
                (fun hd2  ->
                   let fa uu____4810 =
                     match uu____4810 with
                     | (a,q) ->
                         let uu____4823 = ff a in
                         bind uu____4823 (fun a1  -> ret (a1, q)) in
                   let uu____4836 = mapM fa args in
                   bind uu____4836
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4896 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4896 with
               | (bs1,t') ->
                   let uu____4905 =
                     let uu____4908 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4908 t' in
                   bind uu____4905
                     (fun t''  ->
                        let uu____4912 =
                          let uu____4913 =
                            let uu____4930 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4931 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4930, uu____4931, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4913 in
                        ret uu____4912))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4952 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___125_4956 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___125_4956.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___125_4956.FStar_Syntax_Syntax.vars)
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
            let uu____4985 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4985 with
            | (t1,lcomp,g) ->
                let uu____4997 =
                  let uu____4998 = FStar_TypeChecker_Rel.is_trivial g in
                  Prims.op_Negation uu____4998 in
                if uu____4997
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____5005 = new_uvar env typ in
                   bind uu____5005
                     (fun ut  ->
                        log ps
                          (fun uu____5016  ->
                             let uu____5017 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____5018 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____5017 uu____5018);
                        (let uu____5019 =
                           let uu____5022 =
                             let uu____5023 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____5023 typ t1 ut in
                           add_irrelevant_goal env uu____5022 opts in
                         bind uu____5019
                           (fun uu____5026  ->
                              let uu____5027 =
                                bind tau
                                  (fun uu____5032  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____5027))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____5053 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____5053 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____5090  ->
                   let uu____5091 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____5091);
              bind dismiss_all
                (fun uu____5094  ->
                   let uu____5095 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____5095
                     (fun gt'  ->
                        log ps
                          (fun uu____5105  ->
                             let uu____5106 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____5106);
                        (let uu____5107 = push_goals gs in
                         bind uu____5107
                           (fun uu____5111  ->
                              add_goals
                                [(let uu___126_5113 = g in
                                  {
                                    context = (uu___126_5113.context);
                                    witness = (uu___126_5113.witness);
                                    goal_ty = gt';
                                    opts = (uu___126_5113.opts);
                                    is_guard = (uu___126_5113.is_guard)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5133 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____5133 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5145 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5145 with
            | (hd1,args) ->
                let uu____5178 =
                  let uu____5191 =
                    let uu____5192 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5192.FStar_Syntax_Syntax.n in
                  (uu____5191, args) in
                (match uu____5178 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5206::(l,uu____5208)::(r,uu____5210)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5257 =
                       let uu____5258 = do_unify g.context l r in
                       Prims.op_Negation uu____5258 in
                     if uu____5257
                     then
                       let uu____5261 =
                         FStar_TypeChecker_Normalize.term_to_string g.context
                           l in
                       let uu____5262 =
                         FStar_TypeChecker_Normalize.term_to_string g.context
                           r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5261 uu____5262
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5265) ->
                     let uu____5282 =
                       FStar_TypeChecker_Normalize.term_to_string g.context t in
                     fail1 "trefl: not an equality (%s)" uu____5282))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5290 = new_uvar g.context g.goal_ty in
       bind uu____5290
         (fun u  ->
            let g' =
              let uu___127_5297 = g in
              {
                context = (uu___127_5297.context);
                witness = u;
                goal_ty = (uu___127_5297.goal_ty);
                opts = (uu___127_5297.opts);
                is_guard = (uu___127_5297.is_guard)
              } in
            bind dismiss
              (fun uu____5300  ->
                 let uu____5301 =
                   let uu____5304 =
                     let uu____5305 =
                       FStar_TypeChecker_TcTerm.universe_of g.context
                         g.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5305 g.goal_ty u
                       g.witness in
                   add_irrelevant_goal g.context uu____5304 g.opts in
                 bind uu____5301
                   (fun uu____5308  ->
                      let uu____5309 = add_goals [g'] in
                      bind uu____5309 (fun uu____5313  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___128_5330 = ps in
              {
                main_context = (uu___128_5330.main_context);
                main_goal = (uu___128_5330.main_goal);
                all_implicits = (uu___128_5330.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___128_5330.smt_goals)
              })
       | uu____5331 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___129_5346 = ps in
              {
                main_context = (uu___129_5346.main_context);
                main_goal = (uu___129_5346.main_goal);
                all_implicits = (uu___129_5346.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___129_5346.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____5353 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____5395 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____5395 with
         | (t1,typ,guard) ->
             let uu____5411 = FStar_Syntax_Util.head_and_args typ in
             (match uu____5411 with
              | (hd1,args) ->
                  let uu____5454 =
                    let uu____5467 =
                      let uu____5468 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____5468.FStar_Syntax_Syntax.n in
                    (uu____5467, args) in
                  (match uu____5454 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____5487)::(q,uu____5489)::[]) when
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
                         let uu___130_5527 = g in
                         let uu____5528 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____5528;
                           witness = (uu___130_5527.witness);
                           goal_ty = (uu___130_5527.goal_ty);
                           opts = (uu___130_5527.opts);
                           is_guard = (uu___130_5527.is_guard)
                         } in
                       let g2 =
                         let uu___131_5530 = g in
                         let uu____5531 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____5531;
                           witness = (uu___131_5530.witness);
                           goal_ty = (uu___131_5530.goal_ty);
                           opts = (uu___131_5530.opts);
                           is_guard = (uu___131_5530.is_guard)
                         } in
                       bind dismiss
                         (fun uu____5538  ->
                            let uu____5539 = add_goals [g1; g2] in
                            bind uu____5539
                              (fun uu____5548  ->
                                 let uu____5549 =
                                   let uu____5554 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____5555 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____5554, uu____5555) in
                                 ret uu____5549))
                   | uu____5560 ->
                       let uu____5573 =
                         FStar_TypeChecker_Normalize.term_to_string g.context
                           typ in
                       fail1 "Not a disjunction: %s" uu____5573)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5596 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____5596);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___132_5603 = g in
                 {
                   context = (uu___132_5603.context);
                   witness = (uu___132_5603.witness);
                   goal_ty = (uu___132_5603.goal_ty);
                   opts = opts';
                   is_guard = (uu___132_5603.is_guard)
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
           let uu____5644 =
             (goal.context).FStar_TypeChecker_Env.type_of env tm in
           match uu____5644 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5673 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5679 =
              let uu____5680 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5680 in
            new_uvar env uu____5679 in
      bind uu____5673
        (fun typ  ->
           let uu____5692 = new_uvar env typ in
           bind uu____5692 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5712 = do_unify ps.main_context t1 t2 in ret uu____5712)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5732  ->
             let uu____5733 = FStar_Options.unsafe_tactic_exec () in
             if uu____5733
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5739  -> fun uu____5740  -> false) in
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
      let uu____5762 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5762 with
      | (u,uu____5780,g_u) ->
          let g =
            let uu____5795 = FStar_Options.peek () in
            {
              context = env;
              witness = u;
              goal_ty = typ;
              opts = uu____5795;
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
      let uu____5812 = goal_of_goal_ty env typ in
      match uu____5812 with
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