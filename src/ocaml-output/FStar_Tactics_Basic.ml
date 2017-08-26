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
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1685 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1685 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1700 =
             let uu____1701 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1701 in
           if uu____1700
           then fail "Codomain is effectful"
           else
             (let env' = FStar_TypeChecker_Env.push_binders goal.context [b] in
              let typ' = comp_to_typ c in
              let uu____1707 = new_uvar env' typ' in
              bind uu____1707
                (fun u  ->
                   let uu____1714 =
                     let uu____1715 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     FStar_TypeChecker_Rel.teq_nosmt goal.context
                       goal.witness uu____1715 in
                   if uu____1714
                   then
                     let uu____1718 =
                       let uu____1721 =
                         let uu___98_1722 = goal in
                         let uu____1723 = bnorm env' u in
                         let uu____1724 = bnorm env' typ' in
                         {
                           context = env';
                           witness = uu____1723;
                           goal_ty = uu____1724;
                           opts = (uu___98_1722.opts)
                         } in
                       replace_cur uu____1721 in
                     bind uu____1718 (fun uu____1726  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1732 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1732)
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
       (let uu____1753 = FStar_Syntax_Util.arrow_one goal.goal_ty in
        match uu____1753 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1772 =
              let uu____1773 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1773 in
            if uu____1772
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None goal.goal_ty in
               let bs =
                 let uu____1789 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1789; b] in
               let env' = FStar_TypeChecker_Env.push_binders goal.context bs in
               let uu____1791 =
                 let uu____1794 = comp_to_typ c in new_uvar env' uu____1794 in
               bind uu____1791
                 (fun u  ->
                    let lb =
                      let uu____1811 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.goal_ty FStar_Parser_Const.effect_Tot_lid
                        uu____1811 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1815 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1815 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.witness).FStar_Syntax_Syntax.pos in
                        (FStar_Util.print_string "calling teq_nosmt\n";
                         (let res =
                            FStar_TypeChecker_Rel.teq_nosmt goal.context
                              goal.witness tm in
                          if res
                          then
                            let uu____1853 =
                              let uu____1856 =
                                let uu___99_1857 = goal in
                                let uu____1858 = bnorm env' u in
                                let uu____1859 =
                                  let uu____1860 = comp_to_typ c in
                                  bnorm env' uu____1860 in
                                {
                                  context = env';
                                  witness = uu____1858;
                                  goal_ty = uu____1859;
                                  opts = (uu___99_1857.opts)
                                } in
                              replace_cur uu____1856 in
                            bind uu____1853
                              (fun uu____1867  ->
                                 let uu____1868 =
                                   let uu____1873 =
                                     FStar_Syntax_Syntax.mk_binder bv in
                                   (uu____1873, b) in
                                 ret uu____1868)
                          else fail "intro_rec: unification failed"))))
        | FStar_Pervasives_Native.None  ->
            let uu____1887 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1887))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____1912 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1912 in
         let w = normalize steps goal.context goal.witness in
         let t = normalize steps goal.context goal.goal_ty in
         replace_cur
           (let uu___100_1919 = goal in
            {
              context = (uu___100_1919.context);
              witness = w;
              goal_ty = t;
              opts = (uu___100_1919.opts)
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
             let uu____1943 = FStar_TypeChecker_Normalize.tr_norm_steps s in
             FStar_List.append
               [FStar_TypeChecker_Normalize.Reify;
               FStar_TypeChecker_Normalize.UnfoldTac] uu____1943 in
           let t1 = normalize steps ps.main_context t in ret t1)
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
       let uu____1965 = istrivial goal.context goal.goal_ty in
       if uu____1965
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____1970 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1970))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1982 =
           try
             let uu____2010 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____2010
           with
           | e ->
               let uu____2037 = FStar_Syntax_Print.term_to_string t in
               let uu____2038 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____2037
                 uu____2038 in
         bind uu____1982
           (fun uu____2056  ->
              match uu____2056 with
              | (t1,typ,guard) ->
                  let uu____2068 =
                    let uu____2069 =
                      let uu____2070 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2070 in
                    Prims.op_Negation uu____2069 in
                  if uu____2068
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2074 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____2074
                     then (solve goal t1; dismiss)
                     else
                       (let uu____2079 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____2080 =
                          let uu____2081 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____2081 in
                        let uu____2082 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2079 uu____2080 uu____2082))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2094 =
           try
             let uu____2122 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____2122
           with
           | e ->
               let uu____2149 = FStar_Syntax_Print.term_to_string t in
               let uu____2150 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2149
                 uu____2150 in
         bind uu____2094
           (fun uu____2168  ->
              match uu____2168 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2186 =
                       let uu____2187 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2187 in
                     if uu____2186
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2191 =
                          let uu____2200 =
                            let uu____2209 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2209.FStar_Syntax_Syntax.effect_args in
                          match uu____2200 with
                          | pre::post::uu____2220 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2261 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2191 with
                        | (pre,post) ->
                            let uu____2290 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____2290
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____2295  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____2297 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____2298 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____2299 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2297 uu____2298 uu____2299)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____2311 =
          let uu____2318 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____2318 in
        FStar_List.map FStar_Pervasives_Native.fst uu____2311 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2345 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2365 = let uu____2370 = exact tm in trytac uu____2370 in
             bind uu____2365
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2383 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2383 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           let uu____2413 =
                             let uu____2414 =
                               FStar_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu____2414 in
                           if uu____2413
                           then fail "apply: not total codomain"
                           else
                             (let uu____2418 =
                                new_uvar goal.context
                                  bv.FStar_Syntax_Syntax.sort in
                              bind uu____2418
                                (fun u  ->
                                   let tm' =
                                     FStar_Syntax_Syntax.mk_Tm_app tm
                                       [(u, aq)] FStar_Pervasives_Native.None
                                       (goal.context).FStar_TypeChecker_Env.range in
                                   let typ' =
                                     let uu____2438 = comp_to_typ c in
                                     FStar_All.pipe_left
                                       (FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.NT (bv, u)])
                                       uu____2438 in
                                   let uu____2439 = __apply uopt tm' typ' in
                                   bind uu____2439
                                     (fun uu____2446  ->
                                        let uu____2447 =
                                          let uu____2448 =
                                            let uu____2451 =
                                              let uu____2452 =
                                                FStar_Syntax_Util.head_and_args
                                                  u in
                                              FStar_Pervasives_Native.fst
                                                uu____2452 in
                                            FStar_Syntax_Subst.compress
                                              uu____2451 in
                                          uu____2448.FStar_Syntax_Syntax.n in
                                        match uu____2447 with
                                        | FStar_Syntax_Syntax.Tm_uvar
                                            (uvar,uu____2480) ->
                                            bind get
                                              (fun ps  ->
                                                 let uu____2508 =
                                                   uopt &&
                                                     (uvar_free uvar ps) in
                                                 if uu____2508
                                                 then ret ()
                                                 else
                                                   (let uu____2512 =
                                                      let uu____2515 =
                                                        let uu____2516 =
                                                          bnorm goal.context
                                                            u in
                                                        let uu____2517 =
                                                          bnorm goal.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          context =
                                                            (goal.context);
                                                          witness =
                                                            uu____2516;
                                                          goal_ty =
                                                            uu____2517;
                                                          opts = (goal.opts)
                                                        } in
                                                      [uu____2515] in
                                                    add_goals uu____2512))
                                        | uu____2518 -> ret ()))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2575 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____2575 with
           | (tm1,typ,guard) ->
               let uu____2587 =
                 let uu____2588 =
                   let uu____2589 =
                     FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                   FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                     uu____2589 in
                 Prims.op_Negation uu____2588 in
               if uu____2587
               then fail "apply: got non-trivial guard"
               else
                 (let uu____2593 =
                    let uu____2596 = __apply uopt tm1 typ in focus uu____2596 in
                  let uu____2599 =
                    let uu____2602 = FStar_Syntax_Print.term_to_string tm1 in
                    let uu____2603 = FStar_Syntax_Print.term_to_string typ in
                    let uu____2604 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    fail3
                      "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                      uu____2602 uu____2603 uu____2604 in
                  try_unif uu____2593 uu____2599))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let is_unit_t t =
      let uu____2617 =
        let uu____2618 = FStar_Syntax_Subst.compress t in
        uu____2618.FStar_Syntax_Syntax.n in
      match uu____2617 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
          true
      | uu____2622 -> false in
    bind cur_goal
      (fun goal  ->
         let uu____2630 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____2630 with
         | (tm1,t,guard) ->
             let uu____2642 =
               let uu____2643 =
                 let uu____2644 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____2644 in
               Prims.op_Negation uu____2643 in
             if uu____2642
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____2648 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____2648 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2678 =
                         FStar_List.fold_left
                           (fun uu____2724  ->
                              fun uu____2725  ->
                                match (uu____2724, uu____2725) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2828 = is_unit_t b_t in
                                    if uu____2828
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____2866 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.context b_t in
                                       match uu____2866 with
                                       | (u,uu____2896,g_u) ->
                                           let uu____2910 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____2910,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2678 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____2980 =
                             let uu____2989 =
                               let uu____2998 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____2998.FStar_Syntax_Syntax.effect_args in
                             match uu____2989 with
                             | pre::post::uu____3009 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____3050 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____2980 with
                            | (pre,post) ->
                                let uu____3079 =
                                  let uu____3082 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____3082 goal.goal_ty in
                                (match uu____3079 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____3085 =
                                       let uu____3086 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____3086 in
                                     let uu____3087 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____3085 uu____3087
                                 | FStar_Pervasives_Native.Some g ->
                                     let uu____3089 =
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
                                            (fun uu____3160  ->
                                               match uu____3160 with
                                               | (uu____3173,uu____3174,uu____3175,tm2,uu____3177,uu____3178)
                                                   ->
                                                   let uu____3179 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____3179 with
                                                    | (hd1,uu____3195) ->
                                                        let uu____3216 =
                                                          let uu____3217 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____3217.FStar_Syntax_Syntax.n in
                                                        (match uu____3216
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____3220 ->
                                                             true
                                                         | uu____3237 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let uu____3239 =
                                         add_implicits implicits1 in
                                       bind uu____3239
                                         (fun uu____3243  ->
                                            bind dismiss
                                              (fun uu____3252  ->
                                                 let is_free_uvar uv t1 =
                                                   let free_uvars =
                                                     let uu____3263 =
                                                       let uu____3270 =
                                                         FStar_Syntax_Free.uvars
                                                           t1 in
                                                       FStar_Util.set_elements
                                                         uu____3270 in
                                                     FStar_List.map
                                                       FStar_Pervasives_Native.fst
                                                       uu____3263 in
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
                                                   let uu____3311 =
                                                     FStar_Syntax_Util.head_and_args
                                                       t1 in
                                                   match uu____3311 with
                                                   | (hd1,uu____3327) ->
                                                       (match hd1.FStar_Syntax_Syntax.n
                                                        with
                                                        | FStar_Syntax_Syntax.Tm_uvar
                                                            (uv,uu____3349)
                                                            ->
                                                            appears uv goals
                                                        | uu____3374 -> false) in
                                                 let sub_goals =
                                                   FStar_All.pipe_right
                                                     implicits1
                                                     (FStar_List.map
                                                        (fun uu____3415  ->
                                                           match uu____3415
                                                           with
                                                           | (_msg,_env,_uvar,term,typ,uu____3433)
                                                               ->
                                                               let uu____3434
                                                                 =
                                                                 bnorm
                                                                   goal.context
                                                                   term in
                                                               let uu____3435
                                                                 =
                                                                 bnorm
                                                                   goal.context
                                                                   typ in
                                                               {
                                                                 context =
                                                                   (goal.context);
                                                                 witness =
                                                                   uu____3434;
                                                                 goal_ty =
                                                                   uu____3435;
                                                                 opts =
                                                                   (goal.opts)
                                                               })) in
                                                 let rec filter' f xs =
                                                   match xs with
                                                   | [] -> []
                                                   | x::xs1 ->
                                                       let uu____3473 =
                                                         f x xs1 in
                                                       if uu____3473
                                                       then
                                                         let uu____3476 =
                                                           filter' f xs1 in
                                                         x :: uu____3476
                                                       else filter' f xs1 in
                                                 let sub_goals1 =
                                                   filter'
                                                     (fun g1  ->
                                                        fun goals  ->
                                                          let uu____3490 =
                                                            checkone
                                                              g1.witness
                                                              goals in
                                                          Prims.op_Negation
                                                            uu____3490)
                                                     sub_goals in
                                                 let uu____3491 =
                                                   add_irrelevant_goal
                                                     goal.context pre
                                                     goal.opts in
                                                 bind uu____3491
                                                   (fun uu____3496  ->
                                                      let uu____3497 =
                                                        trytac trivial in
                                                      bind uu____3497
                                                        (fun uu____3505  ->
                                                           add_goals
                                                             sub_goals1)))))))))))
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3524 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3524 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3534::(e1,uu____3536)::(e2,uu____3538)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3597 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3620 = destruct_eq' typ in
    match uu____3620 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3650 = FStar_Syntax_Util.un_squash typ in
        (match uu____3650 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3683 =
           FStar_All.pipe_left mlog
             (fun uu____3693  ->
                let uu____3694 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3695 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3694
                  uu____3695) in
         bind uu____3683
           (fun uu____3703  ->
              let uu____3704 =
                let uu____3711 =
                  let uu____3712 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3712 in
                destruct_eq uu____3711 in
              match uu____3704 with
              | FStar_Pervasives_Native.Some (x,e) ->
                  let uu____3729 =
                    let uu____3730 = FStar_Syntax_Subst.compress x in
                    uu____3730.FStar_Syntax_Syntax.n in
                  (match uu____3729 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___107_3737 = goal in
                         let uu____3738 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____3739 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___107_3737.context);
                           witness = uu____3738;
                           goal_ty = uu____3739;
                           opts = (uu___107_3737.opts)
                         } in
                       replace_cur goal1
                   | uu____3740 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3741 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3753 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3753 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let uu____3775 = FStar_Util.set_mem x fns_ty in
           if uu____3775
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____3779 = new_uvar env' goal.goal_ty in
              bind uu____3779
                (fun u  ->
                   let uu____3785 =
                     let uu____3786 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context
                         goal.witness u in
                     Prims.op_Negation uu____3786 in
                   if uu____3785
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___108_3791 = goal in
                        let uu____3792 = bnorm env' u in
                        {
                          context = env';
                          witness = uu____3792;
                          goal_ty = (uu___108_3791.goal_ty);
                          opts = (uu___108_3791.opts)
                        } in
                      bind dismiss (fun uu____3794  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3806 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____3806 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3833 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3833 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____3855 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____3855 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___109_3889 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___109_3889.opts)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3901 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____3901 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____3922 = FStar_Syntax_Print.bv_to_string x in
               let uu____3923 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____3922 uu____3923
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____3941 = revert_all_hd xs1 in
        bind uu____3941 (fun uu____3945  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___110_3962 = g in
           {
             context = ctx';
             witness = (uu___110_3962.witness);
             goal_ty = (uu___110_3962.goal_ty);
             opts = (uu___110_3962.opts)
           } in
         bind dismiss (fun uu____3964  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___111_3981 = g in
           {
             context = ctx';
             witness = (uu___111_3981.witness);
             goal_ty = (uu___111_3981.goal_ty);
             opts = (uu___111_3981.opts)
           } in
         bind dismiss (fun uu____3983  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4025 = f x in
          bind uu____4025
            (fun y  ->
               let uu____4033 = mapM f xs in
               bind uu____4033 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4079 = FStar_Syntax_Subst.compress t in
          uu____4079.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4114 = ff hd1 in
              bind uu____4114
                (fun hd2  ->
                   let fa uu____4134 =
                     match uu____4134 with
                     | (a,q) ->
                         let uu____4147 = ff a in
                         bind uu____4147 (fun a1  -> ret (a1, q)) in
                   let uu____4160 = mapM fa args in
                   bind uu____4160
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4220 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4220 with
               | (bs1,t') ->
                   let uu____4229 =
                     let uu____4232 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4232 t' in
                   bind uu____4229
                     (fun t''  ->
                        let uu____4236 =
                          let uu____4237 =
                            let uu____4254 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4255 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4254, uu____4255, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4237 in
                        ret uu____4236))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4276 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___112_4280 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___112_4280.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___112_4280.FStar_Syntax_Syntax.vars)
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
            let uu____4309 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4309 with
            | (t1,lcomp,g) ->
                let uu____4321 =
                  (let uu____4324 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____4324) ||
                    (let uu____4326 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4326) in
                if uu____4321
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4333 = new_uvar env typ in
                   bind uu____4333
                     (fun ut  ->
                        log ps
                          (fun uu____4344  ->
                             let uu____4345 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4346 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4345 uu____4346);
                        (let uu____4347 =
                           let uu____4350 =
                             let uu____4351 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4351 typ t1 ut in
                           add_irrelevant_goal env uu____4350 opts in
                         bind uu____4347
                           (fun uu____4354  ->
                              let uu____4355 =
                                bind tau
                                  (fun uu____4360  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4355))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4381 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4381 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____4418  ->
                   let uu____4419 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4419);
              bind dismiss_all
                (fun uu____4422  ->
                   let uu____4423 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____4423
                     (fun gt'  ->
                        log ps
                          (fun uu____4433  ->
                             let uu____4434 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4434);
                        (let uu____4435 = push_goals gs in
                         bind uu____4435
                           (fun uu____4439  ->
                              add_goals
                                [(let uu___113_4441 = g in
                                  {
                                    context = (uu___113_4441.context);
                                    witness = (uu___113_4441.witness);
                                    goal_ty = gt';
                                    opts = (uu___113_4441.opts)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4461 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____4461 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4473 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4473 with
            | (hd1,args) ->
                let uu____4506 =
                  let uu____4519 =
                    let uu____4520 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4520.FStar_Syntax_Syntax.n in
                  (uu____4519, args) in
                (match uu____4506 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4534::(l,uu____4536)::(r,uu____4538)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4585 =
                       let uu____4586 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____4586 in
                     if uu____4585
                     then
                       let uu____4589 = FStar_Syntax_Print.term_to_string l in
                       let uu____4590 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4589 uu____4590
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____4594) ->
                     let uu____4611 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____4611))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4619 = new_uvar g.context g.goal_ty in
       bind uu____4619
         (fun u  ->
            let g' =
              let uu___114_4626 = g in
              {
                context = (uu___114_4626.context);
                witness = u;
                goal_ty = (uu___114_4626.goal_ty);
                opts = (uu___114_4626.opts)
              } in
            bind dismiss
              (fun uu____4629  ->
                 let uu____4630 =
                   let uu____4633 =
                     let uu____4634 =
                       FStar_TypeChecker_TcTerm.universe_of g.context
                         g.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4634 g.goal_ty u
                       g.witness in
                   add_irrelevant_goal g.context uu____4633 g.opts in
                 bind uu____4630
                   (fun uu____4637  ->
                      let uu____4638 = add_goals [g'] in
                      bind uu____4638 (fun uu____4642  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___115_4659 = ps in
              {
                main_context = (uu___115_4659.main_context);
                main_goal = (uu___115_4659.main_goal);
                all_implicits = (uu___115_4659.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___115_4659.smt_goals)
              })
       | uu____4660 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___116_4675 = ps in
              {
                main_context = (uu___116_4675.main_context);
                main_goal = (uu___116_4675.main_goal);
                all_implicits = (uu___116_4675.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___116_4675.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____4682 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____4724 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____4724 with
         | (t1,typ,guard) ->
             let uu____4740 = FStar_Syntax_Util.head_and_args typ in
             (match uu____4740 with
              | (hd1,args) ->
                  let uu____4783 =
                    let uu____4796 =
                      let uu____4797 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____4797.FStar_Syntax_Syntax.n in
                    (uu____4796, args) in
                  (match uu____4783 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____4816)::(q,uu____4818)::[]) when
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
                         let uu___117_4856 = g in
                         let uu____4857 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____4857;
                           witness = (uu___117_4856.witness);
                           goal_ty = (uu___117_4856.goal_ty);
                           opts = (uu___117_4856.opts)
                         } in
                       let g2 =
                         let uu___118_4859 = g in
                         let uu____4860 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____4860;
                           witness = (uu___118_4859.witness);
                           goal_ty = (uu___118_4859.goal_ty);
                           opts = (uu___118_4859.opts)
                         } in
                       bind dismiss
                         (fun uu____4867  ->
                            let uu____4868 = add_goals [g1; g2] in
                            bind uu____4868
                              (fun uu____4877  ->
                                 let uu____4878 =
                                   let uu____4883 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____4884 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____4883, uu____4884) in
                                 ret uu____4878))
                   | uu____4889 ->
                       let uu____4902 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____4902)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____4925 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____4925);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___119_4932 = g in
                 {
                   context = (uu___119_4932.context);
                   witness = (uu___119_4932.witness);
                   goal_ty = (uu___119_4932.goal_ty);
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
           let uu____4973 =
             (goal.context).FStar_TypeChecker_Env.type_of env tm in
           match uu____4973 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5002 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5008 =
              let uu____5009 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5009 in
            new_uvar env uu____5008 in
      bind uu____5002
        (fun typ  ->
           let uu____5021 = new_uvar env typ in
           bind uu____5021 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5041 =
             FStar_TypeChecker_Rel.teq_nosmt ps.main_context t1 t2 in
           ret uu____5041)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5061  ->
             let uu____5062 = FStar_Options.unsafe_tactic_exec () in
             if uu____5062
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5068  -> fun uu____5069  -> false) in
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
      let uu____5091 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5091 with
      | (u,uu____5109,g_u) ->
          let g =
            let uu____5124 = FStar_Options.peek () in
            { context = env; witness = u; goal_ty = typ; opts = uu____5124 } in
          (g, g_u)
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (proofstate,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____5141 = goal_of_goal_ty env typ in
      match uu____5141 with
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