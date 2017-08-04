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
  fun p  -> mk_tac (fun uu____1021  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____1030 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____1030
      then ()
      else
        (let uu____1032 =
           let uu____1033 =
             let uu____1034 = FStar_Syntax_Print.term_to_string solution in
             let uu____1035 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____1036 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____1034
               uu____1035 uu____1036 in
           TacFailure uu____1033 in
         FStar_Exn.raise uu____1032)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____1042 =
         let uu___86_1043 = p in
         let uu____1044 = FStar_List.tl p.goals in
         {
           main_context = (uu___86_1043.main_context);
           main_goal = (uu___86_1043.main_goal);
           all_implicits = (uu___86_1043.all_implicits);
           goals = uu____1044;
           smt_goals = (uu___86_1043.smt_goals)
         } in
       set uu____1042)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___87_1053 = p in
          {
            main_context = (uu___87_1053.main_context);
            main_goal = (uu___87_1053.main_goal);
            all_implicits = (uu___87_1053.all_implicits);
            goals = [];
            smt_goals = (uu___87_1053.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___88_1070 = p in
            {
              main_context = (uu___88_1070.main_context);
              main_goal = (uu___88_1070.main_goal);
              all_implicits = (uu___88_1070.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___88_1070.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___89_1087 = p in
            {
              main_context = (uu___89_1087.main_context);
              main_goal = (uu___89_1087.main_goal);
              all_implicits = (uu___89_1087.all_implicits);
              goals = (uu___89_1087.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___90_1104 = p in
            {
              main_context = (uu___90_1104.main_context);
              main_goal = (uu___90_1104.main_goal);
              all_implicits = (uu___90_1104.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___90_1104.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___91_1121 = p in
            {
              main_context = (uu___91_1121.main_context);
              main_goal = (uu___91_1121.main_goal);
              all_implicits = (uu___91_1121.all_implicits);
              goals = (uu___91_1121.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1131  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___92_1144 = p in
            {
              main_context = (uu___92_1144.main_context);
              main_goal = (uu___92_1144.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___92_1144.goals);
              smt_goals = (uu___92_1144.smt_goals)
            }))
let new_uvar: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun typ  ->
      let uu____1169 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____1169 with
      | (u,uu____1185,g_u) ->
          let uu____1199 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____1199 (fun uu____1203  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1208 = FStar_Syntax_Util.un_squash t in
    match uu____1208 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1218 =
          let uu____1219 = FStar_Syntax_Subst.compress t' in
          uu____1219.FStar_Syntax_Syntax.n in
        (match uu____1218 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1223 -> false)
    | uu____1224 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1233 = FStar_Syntax_Util.un_squash t in
    match uu____1233 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1243 =
          let uu____1244 = FStar_Syntax_Subst.compress t' in
          uu____1244.FStar_Syntax_Syntax.n in
        (match uu____1243 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1248 -> false)
    | uu____1249 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let add_irrelevant_goal:
  env ->
    FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun env  ->
    fun phi  ->
      fun opts  ->
        let typ = FStar_Syntax_Util.mk_squash phi in
        let uu____1283 = new_uvar env typ in
        bind uu____1283
          (fun u  ->
             let goal = { context = env; witness = u; goal_ty = typ; opts } in
             add_goals [goal])
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1295 = is_irrelevant g in
       if uu____1295
       then bind dismiss (fun uu____1299  -> add_smt_goals [g])
       else
         (let uu____1301 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1301))
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
             let uu____1347 =
               try
                 let uu____1381 = FStar_List.splitAt n1 p.goals in
                 ret uu____1381
               with | uu____1411 -> fail "divide: not enough goals" in
             bind uu____1347
               (fun uu____1438  ->
                  match uu____1438 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___93_1464 = p in
                        {
                          main_context = (uu___93_1464.main_context);
                          main_goal = (uu___93_1464.main_goal);
                          all_implicits = (uu___93_1464.all_implicits);
                          goals = lgs;
                          smt_goals = []
                        } in
                      let rp =
                        let uu___94_1466 = p in
                        {
                          main_context = (uu___94_1466.main_context);
                          main_goal = (uu___94_1466.main_goal);
                          all_implicits = (uu___94_1466.all_implicits);
                          goals = rgs;
                          smt_goals = []
                        } in
                      let uu____1467 = set lp in
                      bind uu____1467
                        (fun uu____1475  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1489 = set rp in
                                     bind uu____1489
                                       (fun uu____1497  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___95_1513 = p in
                                                      {
                                                        main_context =
                                                          (uu___95_1513.main_context);
                                                        main_goal =
                                                          (uu___95_1513.main_goal);
                                                        all_implicits =
                                                          (uu___95_1513.all_implicits);
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
                                                    let uu____1514 = set p' in
                                                    bind uu____1514
                                                      (fun uu____1522  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1542 = divide (Prims.parse_int "1") f idtac in
    bind uu____1542
      (fun uu____1555  -> match uu____1555 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.goals with
         | [] -> ret []
         | uu____1590::uu____1591 ->
             let uu____1594 =
               let uu____1603 = map tau in
               divide (Prims.parse_int "1") tau uu____1603 in
             bind uu____1594
               (fun uu____1621  ->
                  match uu____1621 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1660 =
        bind t1
          (fun uu____1665  ->
             let uu____1666 = map t2 in
             bind uu____1666 (fun uu____1674  -> ret ())) in
      focus uu____1660
let intro:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 tac
  =
  bind cur_goal
    (fun goal  ->
       let uu____1697 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1697 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1716 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1716 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1751 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1756 =
                  let uu____1757 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1757 in
                if uu____1756
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1779 = new_uvar env' typ' in
                   bind uu____1779
                     (fun u  ->
                        let uu____1790 =
                          let uu____1791 =
                            FStar_Syntax_Util.abs [b1] u
                              FStar_Pervasives_Native.None in
                          FStar_TypeChecker_Rel.teq_nosmt goal.context
                            goal.witness uu____1791 in
                        if uu____1790
                        then
                          let uu____1806 =
                            let uu____1809 =
                              let uu___98_1810 = goal in
                              let uu____1811 = bnorm env' u in
                              let uu____1812 = bnorm env' typ' in
                              {
                                context = env';
                                witness = uu____1811;
                                goal_ty = uu____1812;
                                opts = (uu___98_1810.opts)
                              } in
                            replace_cur uu____1809 in
                          bind uu____1806 (fun uu____1818  -> ret b1)
                        else fail "intro: unification failed")))
       | FStar_Pervasives_Native.None  ->
           let uu____1832 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1832)
let intro_rec:
  (FStar_Syntax_Syntax.binder,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 tac
  =
  bind cur_goal
    (fun goal  ->
       FStar_Util.print_string
         "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
       FStar_Util.print_string
         "WARNING (intro_rec): proceed at your own risk...\n";
       (let uu____1869 = FStar_Syntax_Util.arrow_one goal.goal_ty in
        match uu____1869 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1892 = FStar_Syntax_Subst.open_comp [b] c in
            (match uu____1892 with
             | (bs,c1) ->
                 let b1 =
                   match bs with
                   | b1::[] -> b1
                   | uu____1931 ->
                       failwith
                         "impossible: open_comp returned different amount of binders" in
                 let uu____1936 =
                   let uu____1937 = FStar_Syntax_Util.is_total_comp c1 in
                   Prims.op_Negation uu____1937 in
                 if uu____1936
                 then fail "Codomain is effectful"
                 else
                   (let bv =
                      FStar_Syntax_Syntax.gen_bv "__recf"
                        FStar_Pervasives_Native.None goal.goal_ty in
                    let bs1 =
                      let uu____1961 = FStar_Syntax_Syntax.mk_binder bv in
                      [uu____1961; b1] in
                    let env' =
                      FStar_TypeChecker_Env.push_binders goal.context bs1 in
                    let uu____1971 =
                      let uu____1974 = comp_to_typ c1 in
                      new_uvar env' uu____1974 in
                    bind uu____1971
                      (fun u  ->
                         let lb =
                           let uu____1995 =
                             FStar_Syntax_Util.abs [b1] u
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Util.mk_letbinding
                             (FStar_Util.Inl bv) [] goal.goal_ty
                             FStar_Parser_Const.effect_Tot_lid uu____1995 in
                         let body = FStar_Syntax_Syntax.bv_to_name bv in
                         let uu____2007 =
                           FStar_Syntax_Subst.close_let_rec [lb] body in
                         match uu____2007 with
                         | (lbs,body1) ->
                             let tm =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((true, lbs), body1))
                                 FStar_Pervasives_Native.None
                                 (goal.witness).FStar_Syntax_Syntax.pos in
                             (FStar_Util.print_string "calling teq_nosmt\n";
                              (let res =
                                 FStar_TypeChecker_Rel.teq_nosmt goal.context
                                   goal.witness tm in
                               if res
                               then
                                 let uu____2053 =
                                   let uu____2056 =
                                     let uu___99_2057 = goal in
                                     let uu____2058 = bnorm env' u in
                                     let uu____2059 =
                                       let uu____2060 = comp_to_typ c1 in
                                       bnorm env' uu____2060 in
                                     {
                                       context = env';
                                       witness = uu____2058;
                                       goal_ty = uu____2059;
                                       opts = (uu___99_2057.opts)
                                     } in
                                   replace_cur uu____2056 in
                                 bind uu____2053
                                   (fun uu____2071  ->
                                      let uu____2072 =
                                        let uu____2081 =
                                          FStar_Syntax_Syntax.mk_binder bv in
                                        (uu____2081, b1) in
                                      ret uu____2072)
                               else fail "intro_rec: unification failed")))))
        | FStar_Pervasives_Native.None  ->
            let uu____2107 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2107))
let norm: FStar_Reflection_Data.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let tr s1 =
           match s1 with
           | FStar_Reflection_Data.Simpl  ->
               [FStar_TypeChecker_Normalize.Simplify]
           | FStar_Reflection_Data.WHNF  ->
               [FStar_TypeChecker_Normalize.WHNF]
           | FStar_Reflection_Data.Primops  ->
               [FStar_TypeChecker_Normalize.Primops]
           | FStar_Reflection_Data.Delta  ->
               [FStar_TypeChecker_Normalize.UnfoldUntil
                  FStar_Syntax_Syntax.Delta_constant] in
         let steps =
           let uu____2145 =
             let uu____2148 = FStar_List.map tr s in
             FStar_List.flatten uu____2148 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2145 in
         let w = normalize steps goal.context goal.witness in
         let t = normalize steps goal.context goal.goal_ty in
         replace_cur
           (let uu___100_2159 = goal in
            {
              context = (uu___100_2159.context);
              witness = w;
              goal_ty = t;
              opts = (uu___100_2159.opts)
            }))
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
       let uu____2178 = istrivial goal.context goal.goal_ty in
       if uu____2178
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____2183 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____2183))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2195 =
           try
             let uu____2223 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____2223
           with
           | e ->
               let uu____2250 = FStar_Syntax_Print.term_to_string t in
               let uu____2251 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____2250
                 uu____2251 in
         bind uu____2195
           (fun uu____2269  ->
              match uu____2269 with
              | (t1,typ,guard) ->
                  let uu____2281 =
                    let uu____2282 =
                      let uu____2283 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2283 in
                    Prims.op_Negation uu____2282 in
                  if uu____2281
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2287 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____2287
                     then (solve goal t1; dismiss)
                     else
                       (let uu____2292 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____2293 =
                          let uu____2294 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____2294 in
                        let uu____2295 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2292 uu____2293 uu____2295))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2307 =
           try
             let uu____2335 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____2335
           with
           | e ->
               let uu____2362 = FStar_Syntax_Print.term_to_string t in
               let uu____2363 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2362
                 uu____2363 in
         bind uu____2307
           (fun uu____2381  ->
              match uu____2381 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2399 =
                       let uu____2400 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2400 in
                     if uu____2399
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2404 =
                          let uu____2413 =
                            let uu____2422 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2422.FStar_Syntax_Syntax.effect_args in
                          match uu____2413 with
                          | pre::post::uu____2433 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2474 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2404 with
                        | (pre,post) ->
                            let uu____2503 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____2503
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____2508  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____2510 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____2511 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____2512 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2510 uu____2511 uu____2512)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____2524 =
          let uu____2531 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____2531 in
        FStar_List.map FStar_Pervasives_Native.fst uu____2524 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2569 = let uu____2574 = exact tm in trytac uu____2574 in
           bind uu____2569
             (fun r  ->
                match r with
                | FStar_Pervasives_Native.Some r1 -> ret ()
                | FStar_Pervasives_Native.None  ->
                    let uu____2587 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____2587 with
                     | (tm1,typ,guard) ->
                         let uu____2599 =
                           let uu____2600 =
                             let uu____2601 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____2601 in
                           Prims.op_Negation uu____2600 in
                         if uu____2599
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____2605 = FStar_Syntax_Util.arrow_one typ in
                            match uu____2605 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____2618 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____2618
                            | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                let uu____2634 =
                                  let uu____2635 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2635 in
                                if uu____2634
                                then fail "apply: not total"
                                else
                                  (let uu____2639 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2639
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm1
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.context).FStar_TypeChecker_Env.range in
                                        let uu____2657 = __apply uopt tm' in
                                        bind uu____2657
                                          (fun uu____2664  ->
                                             let uu____2665 =
                                               let uu____2666 =
                                                 let uu____2669 =
                                                   let uu____2670 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2670 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2669 in
                                               uu____2666.FStar_Syntax_Syntax.n in
                                             match uu____2665 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2698) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2726 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2726
                                                      then ret ()
                                                      else
                                                        (let uu____2730 =
                                                           let uu____2733 =
                                                             let uu____2734 =
                                                               bnorm
                                                                 goal.context
                                                                 u in
                                                             let uu____2735 =
                                                               bnorm
                                                                 goal.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               context =
                                                                 (goal.context);
                                                               witness =
                                                                 uu____2734;
                                                               goal_ty =
                                                                 uu____2735;
                                                               opts =
                                                                 (goal.opts)
                                                             } in
                                                           [uu____2733] in
                                                         add_goals uu____2730))
                                             | uu____2736 -> ret ())))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____2745 = __apply true tm in focus uu____2745
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let is_unit_t t =
      let uu____2760 =
        let uu____2761 = FStar_Syntax_Subst.compress t in
        uu____2761.FStar_Syntax_Syntax.n in
      match uu____2760 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
          true
      | uu____2765 -> false in
    bind cur_goal
      (fun goal  ->
         let uu____2773 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____2773 with
         | (tm1,t,guard) ->
             let uu____2785 =
               let uu____2786 =
                 let uu____2787 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____2787 in
               Prims.op_Negation uu____2786 in
             if uu____2785
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____2791 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____2791 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2821 =
                         FStar_List.fold_left
                           (fun uu____2867  ->
                              fun uu____2868  ->
                                match (uu____2867, uu____2868) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2971 = is_unit_t b_t in
                                    if uu____2971
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____3009 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.context b_t in
                                       match uu____3009 with
                                       | (u,uu____3039,g_u) ->
                                           let uu____3053 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____3053,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2821 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____3123 =
                             let uu____3132 =
                               let uu____3141 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____3141.FStar_Syntax_Syntax.effect_args in
                             match uu____3132 with
                             | pre::post::uu____3152 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____3193 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____3123 with
                            | (pre,post) ->
                                let uu____3222 =
                                  let uu____3225 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____3225 goal.goal_ty in
                                (match uu____3222 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____3228 =
                                       let uu____3229 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____3229 in
                                     let uu____3230 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____3228 uu____3230
                                 | FStar_Pervasives_Native.Some g ->
                                     let uu____3232 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         goal.context g in
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____3303  ->
                                               match uu____3303 with
                                               | (uu____3316,uu____3317,uu____3318,tm2,uu____3320,uu____3321)
                                                   ->
                                                   let uu____3322 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____3322 with
                                                    | (hd1,uu____3338) ->
                                                        let uu____3359 =
                                                          let uu____3360 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____3360.FStar_Syntax_Syntax.n in
                                                        (match uu____3359
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____3363 ->
                                                             true
                                                         | uu____3380 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____3390  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____3401 =
                                                 let uu____3408 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____3408 in
                                               FStar_List.map
                                                 FStar_Pervasives_Native.fst
                                                 uu____3401 in
                                             FStar_List.existsML
                                               (fun u  ->
                                                  FStar_Syntax_Unionfind.equiv
                                                    u uv) free_uvars in
                                           let appears uv goals =
                                             FStar_List.existsML
                                               (fun g'  ->
                                                  is_free_uvar uv g'.goal_ty)
                                               goals in
                                           let checkone t1 goals =
                                             let uu____3449 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____3449 with
                                             | (hd1,uu____3465) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____3487) ->
                                                      appears uv goals
                                                  | uu____3512 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____3553  ->
                                                     match uu____3553 with
                                                     | (_msg,_env,_uvar,term,typ,uu____3571)
                                                         ->
                                                         let uu____3572 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____3573 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____3572;
                                                           goal_ty =
                                                             uu____3573;
                                                           opts = (goal.opts)
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____3611 = f x xs1 in
                                                 if uu____3611
                                                 then
                                                   let uu____3614 =
                                                     filter' f xs1 in
                                                   x :: uu____3614
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____3628 =
                                                      checkone g1.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____3628) sub_goals in
                                           let uu____3629 =
                                             add_irrelevant_goal goal.context
                                               pre goal.opts in
                                           bind uu____3629
                                             (fun uu____3634  ->
                                                let uu____3635 =
                                                  trytac trivial in
                                                bind uu____3635
                                                  (fun uu____3644  ->
                                                     let uu____3647 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits in
                                                     bind uu____3647
                                                       (fun uu____3651  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3668 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3668 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3678::(e1,uu____3680)::(e2,uu____3682)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3741 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3764 = destruct_eq' typ in
    match uu____3764 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3794 = FStar_Syntax_Util.un_squash typ in
        (match uu____3794 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3827 =
           FStar_All.pipe_left mlog
             (fun uu____3837  ->
                let uu____3838 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3839 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3838
                  uu____3839) in
         bind uu____3827
           (fun uu____3847  ->
              let uu____3848 =
                let uu____3855 =
                  let uu____3856 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3856 in
                destruct_eq uu____3855 in
              match uu____3848 with
              | FStar_Pervasives_Native.Some (x,e) ->
                  let uu____3873 =
                    let uu____3874 = FStar_Syntax_Subst.compress x in
                    uu____3874.FStar_Syntax_Syntax.n in
                  (match uu____3873 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___105_3881 = goal in
                         let uu____3882 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____3883 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___105_3881.context);
                           witness = uu____3882;
                           goal_ty = uu____3883;
                           opts = (uu___105_3881.opts)
                         } in
                       replace_cur goal1
                   | uu____3884 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3885 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3897 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3897 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let uu____3919 = FStar_Util.set_mem x fns_ty in
           if uu____3919
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____3923 = new_uvar env' goal.goal_ty in
              bind uu____3923
                (fun u  ->
                   let uu____3929 =
                     let uu____3930 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context
                         goal.witness u in
                     Prims.op_Negation uu____3930 in
                   if uu____3929
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___106_3935 = goal in
                        let uu____3936 = bnorm env' u in
                        {
                          context = env';
                          witness = uu____3936;
                          goal_ty = (uu___106_3935.goal_ty);
                          opts = (uu___106_3935.opts)
                        } in
                      bind dismiss (fun uu____3938  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3950 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____3950 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3977 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3977 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____3999 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____3999 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___107_4033 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___107_4033.opts)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4045 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____4045 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4066 = FStar_Syntax_Print.bv_to_string x in
               let uu____4067 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4066 uu____4067
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____4085 = revert_all_hd xs1 in
        bind uu____4085 (fun uu____4089  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___108_4106 = g in
           {
             context = ctx';
             witness = (uu___108_4106.witness);
             goal_ty = (uu___108_4106.goal_ty);
             opts = (uu___108_4106.opts)
           } in
         bind dismiss (fun uu____4108  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___109_4125 = g in
           {
             context = ctx';
             witness = (uu___109_4125.witness);
             goal_ty = (uu___109_4125.goal_ty);
             opts = (uu___109_4125.opts)
           } in
         bind dismiss (fun uu____4127  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4169 = f x in
          bind uu____4169
            (fun y  ->
               let uu____4177 = mapM f xs in
               bind uu____4177 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4223 = FStar_Syntax_Subst.compress t in
          uu____4223.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4258 = ff hd1 in
              bind uu____4258
                (fun hd2  ->
                   let fa uu____4278 =
                     match uu____4278 with
                     | (a,q) ->
                         let uu____4291 = ff a in
                         bind uu____4291 (fun a1  -> ret (a1, q)) in
                   let uu____4304 = mapM fa args in
                   bind uu____4304
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4364 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4364 with
               | (bs1,t') ->
                   let uu____4373 =
                     let uu____4376 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4376 t' in
                   bind uu____4373
                     (fun t''  ->
                        let uu____4380 =
                          let uu____4381 =
                            let uu____4398 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4399 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4398, uu____4399, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4381 in
                        ret uu____4380))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4420 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___110_4424 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___110_4424.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___110_4424.FStar_Syntax_Syntax.vars)
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
            let uu____4453 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4453 with
            | (t1,lcomp,g) ->
                let uu____4465 =
                  (let uu____4468 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____4468) ||
                    (let uu____4470 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4470) in
                if uu____4465
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4477 = new_uvar env typ in
                   bind uu____4477
                     (fun ut  ->
                        log ps
                          (fun uu____4488  ->
                             let uu____4489 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4490 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4489 uu____4490);
                        (let uu____4491 =
                           let uu____4494 =
                             let uu____4495 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4495 typ t1 ut in
                           add_irrelevant_goal env uu____4494 opts in
                         bind uu____4491
                           (fun uu____4498  ->
                              let uu____4499 =
                                bind tau
                                  (fun uu____4504  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4499))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4525 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4525 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____4562  ->
                   let uu____4563 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4563);
              bind dismiss_all
                (fun uu____4566  ->
                   let uu____4567 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____4567
                     (fun gt'  ->
                        log ps
                          (fun uu____4577  ->
                             let uu____4578 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4578);
                        (let uu____4579 = push_goals gs in
                         bind uu____4579
                           (fun uu____4583  ->
                              add_goals
                                [(let uu___111_4585 = g in
                                  {
                                    context = (uu___111_4585.context);
                                    witness = (uu___111_4585.witness);
                                    goal_ty = gt';
                                    opts = (uu___111_4585.opts)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4605 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____4605 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4617 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4617 with
            | (hd1,args) ->
                let uu____4650 =
                  let uu____4663 =
                    let uu____4664 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4664.FStar_Syntax_Syntax.n in
                  (uu____4663, args) in
                (match uu____4650 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4678::(l,uu____4680)::(r,uu____4682)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4729 =
                       let uu____4730 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____4730 in
                     if uu____4729
                     then
                       let uu____4733 = FStar_Syntax_Print.term_to_string l in
                       let uu____4734 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4733 uu____4734
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____4738) ->
                     let uu____4755 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____4755))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4763 = new_uvar g.context g.goal_ty in
       bind uu____4763
         (fun u  ->
            let g' =
              let uu___112_4770 = g in
              {
                context = (uu___112_4770.context);
                witness = u;
                goal_ty = (uu___112_4770.goal_ty);
                opts = (uu___112_4770.opts)
              } in
            bind dismiss
              (fun uu____4773  ->
                 let uu____4774 =
                   let uu____4777 =
                     let uu____4778 =
                       FStar_TypeChecker_TcTerm.universe_of g.context
                         g.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4778 g.goal_ty u
                       g.witness in
                   add_irrelevant_goal g.context uu____4777 g.opts in
                 bind uu____4774
                   (fun uu____4781  ->
                      let uu____4782 = add_goals [g'] in
                      bind uu____4782 (fun uu____4786  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___113_4803 = ps in
              {
                main_context = (uu___113_4803.main_context);
                main_goal = (uu___113_4803.main_goal);
                all_implicits = (uu___113_4803.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___113_4803.smt_goals)
              })
       | uu____4804 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___114_4819 = ps in
              {
                main_context = (uu___114_4819.main_context);
                main_goal = (uu___114_4819.main_goal);
                all_implicits = (uu___114_4819.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___114_4819.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____4826 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____4868 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____4868 with
         | (t1,typ,guard) ->
             let uu____4884 = FStar_Syntax_Util.head_and_args typ in
             (match uu____4884 with
              | (hd1,args) ->
                  let uu____4927 =
                    let uu____4940 =
                      let uu____4941 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____4941.FStar_Syntax_Syntax.n in
                    (uu____4940, args) in
                  (match uu____4927 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____4960)::(q,uu____4962)::[]) when
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
                         let uu___115_5000 = g in
                         let uu____5001 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____5001;
                           witness = (uu___115_5000.witness);
                           goal_ty = (uu___115_5000.goal_ty);
                           opts = (uu___115_5000.opts)
                         } in
                       let g2 =
                         let uu___116_5003 = g in
                         let uu____5004 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____5004;
                           witness = (uu___116_5003.witness);
                           goal_ty = (uu___116_5003.goal_ty);
                           opts = (uu___116_5003.opts)
                         } in
                       bind dismiss
                         (fun uu____5011  ->
                            let uu____5012 = add_goals [g1; g2] in
                            bind uu____5012
                              (fun uu____5021  ->
                                 let uu____5022 =
                                   let uu____5027 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____5028 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____5027, uu____5028) in
                                 ret uu____5022))
                   | uu____5033 ->
                       let uu____5046 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____5046)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5069 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____5069);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___117_5076 = g in
                 {
                   context = (uu___117_5076.context);
                   witness = (uu___117_5076.witness);
                   goal_ty = (uu___117_5076.goal_ty);
                   opts = opts'
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
           let uu____5117 =
             (goal.context).FStar_TypeChecker_Env.type_of env tm in
           match uu____5117 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5146 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5152 =
              let uu____5153 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5153 in
            new_uvar env uu____5152 in
      bind uu____5146
        (fun typ  ->
           let uu____5165 = new_uvar env typ in
           bind uu____5165 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5185 =
             FStar_TypeChecker_Rel.teq_nosmt ps.main_context t1 t2 in
           ret uu____5185)
let goal_of_goal_ty:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (goal,FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____5206 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5206 with
      | (u,uu____5224,g_u) ->
          let g =
            let uu____5239 = FStar_Options.peek () in
            { context = env; witness = u; goal_ty = typ; opts = uu____5239 } in
          (g, g_u)
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (proofstate,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____5256 = goal_of_goal_ty env typ in
      match uu____5256 with
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