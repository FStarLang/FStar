open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let bnorm:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun e  -> fun t  -> FStar_TypeChecker_Normalize.normalize [] e t
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
    match projectee with | Success _0 -> true | uu____195 -> false
let __proj__Success__item___0:
  'a . 'a result -> ('a,proofstate) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: 'a . 'a result -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____241 -> false
let __proj__Failed__item___0:
  'a . 'a result -> (Prims.string,proofstate) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Failed _0 -> _0
exception TacFailure of Prims.string
let uu___is_TacFailure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | TacFailure uu____276 -> true | uu____277 -> false
let __proj__TacFailure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | TacFailure uu____285 -> uu____285
type 'a tac = {
  tac_f: proofstate -> 'a result;}
let __proj__Mktac__item__tac_f: 'a . 'a tac -> proofstate -> 'a result =
  fun projectee  ->
    match projectee with | { tac_f = __fname__tac_f;_} -> __fname__tac_f
let mk_tac: 'a . (proofstate -> 'a result) -> 'a tac =
  fun f  -> { tac_f = f }
let run: 'Auu____349 . 'Auu____349 tac -> proofstate -> 'Auu____349 result =
  fun t  -> fun p  -> t.tac_f p
let ret: 'a . 'a -> 'a tac = fun x  -> mk_tac (fun p  -> Success (x, p))
let bind: 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____416 = run t1 p in
           match uu____416 with
           | Success (a,q) -> let uu____423 = t2 a in run uu____423 q
           | Failed (msg,q) -> Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____435 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____435
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____436 = FStar_Syntax_Print.term_to_string g.witness in
    let uu____437 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____436 uu____437
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____450 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____450
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____463 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____463
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____480 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____480
let comp_to_typ: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____486) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____496) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: goal -> Prims.bool =
  fun g  ->
    let uu____510 =
      let uu____515 =
        FStar_TypeChecker_Normalize.unfold_whnf g.context g.goal_ty in
      FStar_Syntax_Util.un_squash uu____515 in
    match uu____510 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____521 -> false
let dump_goal: 'Auu____532 . 'Auu____532 -> goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____542 = goal_to_string goal in tacprint uu____542
let dump_cur: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____552 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____556 = FStar_List.hd ps.goals in dump_goal ps uu____556))
let ps_to_string:
  (Prims.string,proofstate) FStar_Pervasives_Native.tuple2 -> Prims.string =
  fun uu____564  ->
    match uu____564 with
    | (msg,ps) ->
        let uu____571 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
        let uu____572 =
          let uu____573 = FStar_List.map goal_to_string ps.goals in
          FStar_String.concat "\n" uu____573 in
        let uu____576 =
          FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
        let uu____577 =
          let uu____578 = FStar_List.map goal_to_string ps.smt_goals in
          FStar_String.concat "\n" uu____578 in
        FStar_Util.format5
          "State dump (%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s" msg
          uu____571 uu____572 uu____576 uu____577
let goal_to_json: goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____586 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____586 FStar_Syntax_Print.binders_to_json in
    let uu____587 =
      let uu____594 =
        let uu____601 =
          let uu____606 =
            let uu____607 =
              let uu____614 =
                let uu____619 =
                  let uu____620 = FStar_Syntax_Print.term_to_string g.witness in
                  FStar_Util.JsonStr uu____620 in
                ("witness", uu____619) in
              let uu____621 =
                let uu____628 =
                  let uu____633 =
                    let uu____634 =
                      FStar_Syntax_Print.term_to_string g.goal_ty in
                    FStar_Util.JsonStr uu____634 in
                  ("type", uu____633) in
                [uu____628] in
              uu____614 :: uu____621 in
            FStar_Util.JsonAssoc uu____607 in
          ("goal", uu____606) in
        [uu____601] in
      ("hyps", g_binders) :: uu____594 in
    FStar_Util.JsonAssoc uu____587
let ps_to_json:
  (Prims.string,proofstate) FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____666  ->
    match uu____666 with
    | (msg,ps) ->
        let uu____673 =
          let uu____680 =
            let uu____687 =
              let uu____692 =
                let uu____693 = FStar_List.map goal_to_json ps.goals in
                FStar_Util.JsonList uu____693 in
              ("goals", uu____692) in
            let uu____696 =
              let uu____703 =
                let uu____708 =
                  let uu____709 = FStar_List.map goal_to_json ps.smt_goals in
                  FStar_Util.JsonList uu____709 in
                ("smt-goals", uu____708) in
              [uu____703] in
            uu____687 :: uu____696 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____680 in
        FStar_Util.JsonAssoc uu____673
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____738  ->
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
      let uu____798 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____798 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____820 =
              let uu____823 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____823 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____820);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail: 'Auu____863 . Prims.string -> 'Auu____863 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____874 =
            FStar_TypeChecker_Env.debug ps.main_context
              (FStar_Options.Other "TacFail") in
          if uu____874
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         Failed (msg, ps))
let fail1: 'Auu____882 . Prims.string -> Prims.string -> 'Auu____882 tac =
  fun msg  ->
    fun x  -> let uu____893 = FStar_Util.format1 msg x in fail uu____893
let fail2:
  'Auu____902 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____902 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____917 = FStar_Util.format2 msg x y in fail uu____917
let fail3:
  'Auu____928 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____928 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____947 = FStar_Util.format3 msg x y z in fail uu____947
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____975 = run t ps in
         match uu____975 with
         | Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              Success ((FStar_Pervasives_Native.Some a), q))
         | Failed (uu____989,uu____990) ->
             (FStar_Syntax_Unionfind.rollback tx;
              Success (FStar_Pervasives_Native.None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____1005  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____1014 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____1014
      then ()
      else
        (let uu____1016 =
           let uu____1017 =
             let uu____1018 = FStar_Syntax_Print.term_to_string solution in
             let uu____1019 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____1020 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____1018
               uu____1019 uu____1020 in
           TacFailure uu____1017 in
         FStar_Exn.raise uu____1016)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____1026 =
         let uu___86_1027 = p in
         let uu____1028 = FStar_List.tl p.goals in
         {
           main_context = (uu___86_1027.main_context);
           main_goal = (uu___86_1027.main_goal);
           all_implicits = (uu___86_1027.all_implicits);
           goals = uu____1028;
           smt_goals = (uu___86_1027.smt_goals)
         } in
       set uu____1026)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___87_1037 = p in
          {
            main_context = (uu___87_1037.main_context);
            main_goal = (uu___87_1037.main_goal);
            all_implicits = (uu___87_1037.all_implicits);
            goals = [];
            smt_goals = (uu___87_1037.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___88_1054 = p in
            {
              main_context = (uu___88_1054.main_context);
              main_goal = (uu___88_1054.main_goal);
              all_implicits = (uu___88_1054.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___88_1054.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___89_1071 = p in
            {
              main_context = (uu___89_1071.main_context);
              main_goal = (uu___89_1071.main_goal);
              all_implicits = (uu___89_1071.all_implicits);
              goals = (uu___89_1071.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___90_1088 = p in
            {
              main_context = (uu___90_1088.main_context);
              main_goal = (uu___90_1088.main_goal);
              all_implicits = (uu___90_1088.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___90_1088.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___91_1105 = p in
            {
              main_context = (uu___91_1105.main_context);
              main_goal = (uu___91_1105.main_goal);
              all_implicits = (uu___91_1105.all_implicits);
              goals = (uu___91_1105.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1115  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___92_1128 = p in
            {
              main_context = (uu___92_1128.main_context);
              main_goal = (uu___92_1128.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___92_1128.goals);
              smt_goals = (uu___92_1128.smt_goals)
            }))
let new_uvar:
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2 tac
  =
  fun env  ->
    fun typ  ->
      let uu____1161 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____1161 with
      | (u,uu____1181,g_u) ->
          let uu____1195 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____1195 (fun uu____1203  -> ret (u, g_u))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1212 = FStar_Syntax_Util.un_squash t in
    match uu____1212 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1222 =
          let uu____1223 = FStar_Syntax_Subst.compress t' in
          uu____1223.FStar_Syntax_Syntax.n in
        (match uu____1222 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1227 -> false)
    | uu____1228 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1237 = FStar_Syntax_Util.un_squash t in
    match uu____1237 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1247 =
          let uu____1248 = FStar_Syntax_Subst.compress t' in
          uu____1248.FStar_Syntax_Syntax.n in
        (match uu____1247 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1252 -> false)
    | uu____1253 -> false
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
        let uu____1287 = new_uvar env typ in
        bind uu____1287
          (fun uu____1302  ->
             match uu____1302 with
             | (u,g_u) ->
                 let goal =
                   { context = env; witness = u; goal_ty = typ; opts } in
                 add_goals [goal])
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1317 = is_irrelevant g in
       if uu____1317
       then bind dismiss (fun uu____1321  -> add_smt_goals [g])
       else
         (let uu____1323 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1323))
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
             let uu____1369 =
               try
                 let uu____1403 = FStar_List.splitAt n1 p.goals in
                 ret uu____1403
               with | uu____1433 -> fail "divide: not enough goals" in
             bind uu____1369
               (fun uu____1460  ->
                  match uu____1460 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___93_1486 = p in
                        {
                          main_context = (uu___93_1486.main_context);
                          main_goal = (uu___93_1486.main_goal);
                          all_implicits = (uu___93_1486.all_implicits);
                          goals = lgs;
                          smt_goals = []
                        } in
                      let rp =
                        let uu___94_1488 = p in
                        {
                          main_context = (uu___94_1488.main_context);
                          main_goal = (uu___94_1488.main_goal);
                          all_implicits = (uu___94_1488.all_implicits);
                          goals = rgs;
                          smt_goals = []
                        } in
                      let uu____1489 = set lp in
                      bind uu____1489
                        (fun uu____1497  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1511 = set rp in
                                     bind uu____1511
                                       (fun uu____1519  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___95_1535 = p in
                                                      {
                                                        main_context =
                                                          (uu___95_1535.main_context);
                                                        main_goal =
                                                          (uu___95_1535.main_goal);
                                                        all_implicits =
                                                          (uu___95_1535.all_implicits);
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
                                                    let uu____1536 = set p' in
                                                    bind uu____1536
                                                      (fun uu____1544  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1564 = divide (Prims.parse_int "1") f idtac in
    bind uu____1564
      (fun uu____1577  -> match uu____1577 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.goals with
         | [] -> ret []
         | uu____1612::uu____1613 ->
             let uu____1616 =
               let uu____1625 = map tau in
               divide (Prims.parse_int "1") tau uu____1625 in
             bind uu____1616
               (fun uu____1643  ->
                  match uu____1643 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1682 =
        bind t1
          (fun uu____1687  ->
             let uu____1688 = map t2 in
             bind uu____1688 (fun uu____1696  -> ret ())) in
      focus uu____1682
let intro:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 tac
  =
  bind cur_goal
    (fun goal  ->
       let uu____1719 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1719 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1738 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1738 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1773 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1778 =
                  let uu____1779 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1779 in
                if uu____1778
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1801 = new_uvar env' typ' in
                   bind uu____1801
                     (fun uu____1821  ->
                        match uu____1821 with
                        | (u,g) ->
                            let uu____1834 =
                              let uu____1835 =
                                FStar_Syntax_Util.abs [b1] u
                                  FStar_Pervasives_Native.None in
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                goal.witness uu____1835 in
                            if uu____1834
                            then
                              let uu____1850 =
                                let uu____1853 =
                                  let uu___98_1854 = goal in
                                  let uu____1855 = bnorm env' u in
                                  let uu____1856 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1855;
                                    goal_ty = uu____1856;
                                    opts = (uu___98_1854.opts)
                                  } in
                                replace_cur uu____1853 in
                              bind uu____1850 (fun uu____1862  -> ret b1)
                            else fail "intro: unification failed")))
       | FStar_Pervasives_Native.None  ->
           let uu____1876 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1876)
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
       (let uu____1913 = FStar_Syntax_Util.arrow_one goal.goal_ty in
        match uu____1913 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1936 = FStar_Syntax_Subst.open_comp [b] c in
            (match uu____1936 with
             | (bs,c1) ->
                 let b1 =
                   match bs with
                   | b1::[] -> b1
                   | uu____1975 ->
                       failwith
                         "impossible: open_comp returned different amount of binders" in
                 let uu____1980 =
                   let uu____1981 = FStar_Syntax_Util.is_total_comp c1 in
                   Prims.op_Negation uu____1981 in
                 if uu____1980
                 then fail "Codomain is effectful"
                 else
                   (let bv =
                      FStar_Syntax_Syntax.gen_bv "__recf"
                        FStar_Pervasives_Native.None goal.goal_ty in
                    let bs1 =
                      let uu____2005 = FStar_Syntax_Syntax.mk_binder bv in
                      [uu____2005; b1] in
                    let env' =
                      FStar_TypeChecker_Env.push_binders goal.context bs1 in
                    let uu____2015 =
                      let uu____2022 = comp_to_typ c1 in
                      new_uvar env' uu____2022 in
                    bind uu____2015
                      (fun uu____2047  ->
                         match uu____2047 with
                         | (u,g) ->
                             let lb =
                               let uu____2065 =
                                 FStar_Syntax_Util.abs [b1] u
                                   FStar_Pervasives_Native.None in
                               FStar_Syntax_Util.mk_letbinding
                                 (FStar_Util.Inl bv) [] goal.goal_ty
                                 FStar_Parser_Const.effect_Tot_lid uu____2065 in
                             let body = FStar_Syntax_Syntax.bv_to_name bv in
                             let uu____2077 =
                               FStar_Syntax_Subst.close_let_rec [lb] body in
                             (match uu____2077 with
                              | (lbs,body1) ->
                                  let tm =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((true, lbs), body1))
                                      FStar_Pervasives_Native.None
                                      (goal.witness).FStar_Syntax_Syntax.pos in
                                  (FStar_Util.print_string
                                     "calling teq_nosmt\n";
                                   (let res =
                                      FStar_TypeChecker_Rel.teq_nosmt
                                        goal.context goal.witness tm in
                                    if res
                                    then
                                      let uu____2123 =
                                        let uu____2126 =
                                          let uu___99_2127 = goal in
                                          let uu____2128 = bnorm env' u in
                                          let uu____2129 =
                                            let uu____2130 = comp_to_typ c1 in
                                            bnorm env' uu____2130 in
                                          {
                                            context = env';
                                            witness = uu____2128;
                                            goal_ty = uu____2129;
                                            opts = (uu___99_2127.opts)
                                          } in
                                        replace_cur uu____2126 in
                                      bind uu____2123
                                        (fun uu____2141  ->
                                           let uu____2142 =
                                             let uu____2151 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 bv in
                                             (uu____2151, b1) in
                                           ret uu____2142)
                                    else fail "intro_rec: unification failed"))))))
        | FStar_Pervasives_Native.None  ->
            let uu____2177 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2177))
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
           let uu____2215 =
             let uu____2218 = FStar_List.map tr s in
             FStar_List.flatten uu____2218 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2215 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___100_2229 = goal in
            {
              context = (uu___100_2229.context);
              witness = w;
              goal_ty = t;
              opts = (uu___100_2229.opts)
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
      let t1 = FStar_TypeChecker_Normalize.normalize steps e t in is_true t1
let trivial: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2248 = istrivial goal.context goal.goal_ty in
       if uu____2248
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____2253 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____2253))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2265 =
           try
             let uu____2293 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____2293
           with
           | e ->
               let uu____2320 = FStar_Syntax_Print.term_to_string t in
               let uu____2321 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____2320
                 uu____2321 in
         bind uu____2265
           (fun uu____2339  ->
              match uu____2339 with
              | (t1,typ,guard) ->
                  let uu____2351 =
                    let uu____2352 =
                      let uu____2353 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2353 in
                    Prims.op_Negation uu____2352 in
                  if uu____2351
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2357 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____2357
                     then (solve goal t1; dismiss)
                     else
                       (let uu____2362 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____2363 =
                          let uu____2364 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____2364 in
                        let uu____2365 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2362 uu____2363 uu____2365))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2377 =
           try
             let uu____2405 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____2405
           with
           | e ->
               let uu____2432 = FStar_Syntax_Print.term_to_string t in
               let uu____2433 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2432
                 uu____2433 in
         bind uu____2377
           (fun uu____2451  ->
              match uu____2451 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2469 =
                       let uu____2470 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2470 in
                     if uu____2469
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2474 =
                          let uu____2483 =
                            let uu____2492 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2492.FStar_Syntax_Syntax.effect_args in
                          match uu____2483 with
                          | pre::post::uu____2503 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2544 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2474 with
                        | (pre,post) ->
                            let uu____2573 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____2573
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____2578  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____2580 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____2581 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____2582 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2580 uu____2581 uu____2582)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____2594 =
          let uu____2601 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____2601 in
        FStar_List.map FStar_Pervasives_Native.fst uu____2594 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2639 = let uu____2644 = exact tm in trytac uu____2644 in
           bind uu____2639
             (fun r  ->
                match r with
                | FStar_Pervasives_Native.Some r1 -> ret ()
                | FStar_Pervasives_Native.None  ->
                    let uu____2657 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____2657 with
                     | (tm1,typ,guard) ->
                         let uu____2669 =
                           let uu____2670 =
                             let uu____2671 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____2671 in
                           Prims.op_Negation uu____2670 in
                         if uu____2669
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____2675 = FStar_Syntax_Util.arrow_one typ in
                            match uu____2675 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____2688 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____2688
                            | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                let uu____2704 =
                                  let uu____2705 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2705 in
                                if uu____2704
                                then fail "apply: not total"
                                else
                                  (let uu____2709 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2709
                                     (fun uu____2725  ->
                                        match uu____2725 with
                                        | (u,g_u) ->
                                            let tm' =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                tm1 [(u, aq)]
                                                FStar_Pervasives_Native.None
                                                (goal.context).FStar_TypeChecker_Env.range in
                                            let uu____2745 = __apply uopt tm' in
                                            bind uu____2745
                                              (fun uu____2752  ->
                                                 let uu____2753 =
                                                   let uu____2754 =
                                                     let uu____2757 =
                                                       let uu____2758 =
                                                         FStar_Syntax_Util.head_and_args
                                                           u in
                                                       FStar_Pervasives_Native.fst
                                                         uu____2758 in
                                                     FStar_Syntax_Subst.compress
                                                       uu____2757 in
                                                   uu____2754.FStar_Syntax_Syntax.n in
                                                 match uu____2753 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     (uvar,uu____2786) ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____2814 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____2814
                                                          then ret ()
                                                          else
                                                            (let uu____2818 =
                                                               let uu____2821
                                                                 =
                                                                 let uu____2822
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____2823
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____2822;
                                                                   goal_ty =
                                                                    uu____2823;
                                                                   opts =
                                                                    (goal.opts)
                                                                 } in
                                                               [uu____2821] in
                                                             add_goals
                                                               uu____2818))
                                                 | uu____2824 -> ret ())))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____2833 = __apply true tm in focus uu____2833
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let is_unit_t t =
      let uu____2848 =
        let uu____2849 = FStar_Syntax_Subst.compress t in
        uu____2849.FStar_Syntax_Syntax.n in
      match uu____2848 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
          true
      | uu____2853 -> false in
    bind cur_goal
      (fun goal  ->
         let uu____2861 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____2861 with
         | (tm1,t,guard) ->
             let uu____2873 =
               let uu____2874 =
                 let uu____2875 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____2875 in
               Prims.op_Negation uu____2874 in
             if uu____2873
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____2879 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____2879 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2909 =
                         FStar_List.fold_left
                           (fun uu____2955  ->
                              fun uu____2956  ->
                                match (uu____2955, uu____2956) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____3059 = is_unit_t b_t in
                                    if uu____3059
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____3097 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.context b_t in
                                       match uu____3097 with
                                       | (u,uu____3127,g_u) ->
                                           let uu____3141 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____3141,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2909 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____3211 =
                             let uu____3220 =
                               let uu____3229 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____3229.FStar_Syntax_Syntax.effect_args in
                             match uu____3220 with
                             | pre::post::uu____3240 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____3281 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____3211 with
                            | (pre,post) ->
                                let uu____3310 =
                                  let uu____3313 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____3313 goal.goal_ty in
                                (match uu____3310 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____3316 =
                                       let uu____3317 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____3317 in
                                     let uu____3318 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____3316 uu____3318
                                 | FStar_Pervasives_Native.Some g ->
                                     let uu____3320 =
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
                                            (fun uu____3391  ->
                                               match uu____3391 with
                                               | (uu____3404,uu____3405,uu____3406,tm2,uu____3408,uu____3409)
                                                   ->
                                                   let uu____3410 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____3410 with
                                                    | (hd1,uu____3426) ->
                                                        let uu____3447 =
                                                          let uu____3448 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____3448.FStar_Syntax_Syntax.n in
                                                        (match uu____3447
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____3451 ->
                                                             true
                                                         | uu____3468 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____3478  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____3489 =
                                                 let uu____3496 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____3496 in
                                               FStar_List.map
                                                 FStar_Pervasives_Native.fst
                                                 uu____3489 in
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
                                             let uu____3537 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____3537 with
                                             | (hd1,uu____3553) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____3575) ->
                                                      appears uv goals
                                                  | uu____3600 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____3641  ->
                                                     match uu____3641 with
                                                     | (_msg,_env,_uvar,term,typ,uu____3659)
                                                         ->
                                                         let uu____3660 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____3661 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____3660;
                                                           goal_ty =
                                                             uu____3661;
                                                           opts = (goal.opts)
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____3699 = f x xs1 in
                                                 if uu____3699
                                                 then
                                                   let uu____3702 =
                                                     filter' f xs1 in
                                                   x :: uu____3702
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____3716 =
                                                      checkone g1.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____3716) sub_goals in
                                           let uu____3717 =
                                             add_irrelevant_goal goal.context
                                               pre goal.opts in
                                           bind uu____3717
                                             (fun uu____3722  ->
                                                let uu____3723 =
                                                  trytac trivial in
                                                bind uu____3723
                                                  (fun uu____3732  ->
                                                     let uu____3735 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits in
                                                     bind uu____3735
                                                       (fun uu____3739  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3756 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3756 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3766::(e1,uu____3768)::(e2,uu____3770)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3829 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3852 = destruct_eq' typ in
    match uu____3852 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3882 = FStar_Syntax_Util.un_squash typ in
        (match uu____3882 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3915 =
           FStar_All.pipe_left mlog
             (fun uu____3925  ->
                let uu____3926 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3927 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3926
                  uu____3927) in
         bind uu____3915
           (fun uu____3935  ->
              let uu____3936 =
                let uu____3943 =
                  let uu____3944 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3944 in
                destruct_eq uu____3943 in
              match uu____3936 with
              | FStar_Pervasives_Native.Some (x,e) ->
                  let uu____3961 =
                    let uu____3962 = FStar_Syntax_Subst.compress x in
                    uu____3962.FStar_Syntax_Syntax.n in
                  (match uu____3961 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___105_3969 = goal in
                         let uu____3970 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____3971 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___105_3969.context);
                           witness = uu____3970;
                           goal_ty = uu____3971;
                           opts = (uu___105_3969.opts)
                         } in
                       replace_cur goal1
                   | uu____3972 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3973 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3985 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3985 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let uu____4007 = FStar_Util.set_mem x fns_ty in
           if uu____4007
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4011 = new_uvar env' goal.goal_ty in
              bind uu____4011
                (fun uu____4026  ->
                   match uu____4026 with
                   | (u,g) ->
                       let uu____4035 =
                         let uu____4036 =
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness u in
                         Prims.op_Negation uu____4036 in
                       if uu____4035
                       then fail "clear: unification failed"
                       else
                         (let new_goal =
                            let uu___106_4041 = goal in
                            let uu____4042 = bnorm env' u in
                            {
                              context = env';
                              witness = uu____4042;
                              goal_ty = (uu___106_4041.goal_ty);
                              opts = (uu___106_4041.opts)
                            } in
                          bind dismiss
                            (fun uu____4044  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4056 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____4056 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4083 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____4083 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4105 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4105 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___107_4139 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___107_4139.opts)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4151 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____4151 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4172 = FStar_Syntax_Print.bv_to_string x in
               let uu____4173 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4172 uu____4173
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____4191 = revert_all_hd xs1 in
        bind uu____4191 (fun uu____4195  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___108_4212 = g in
           {
             context = ctx';
             witness = (uu___108_4212.witness);
             goal_ty = (uu___108_4212.goal_ty);
             opts = (uu___108_4212.opts)
           } in
         bind dismiss (fun uu____4214  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___109_4231 = g in
           {
             context = ctx';
             witness = (uu___109_4231.witness);
             goal_ty = (uu___109_4231.goal_ty);
             opts = (uu___109_4231.opts)
           } in
         bind dismiss (fun uu____4233  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4275 = f x in
          bind uu____4275
            (fun y  ->
               let uu____4283 = mapM f xs in
               bind uu____4283 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4329 = FStar_Syntax_Subst.compress t in
          uu____4329.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4364 = ff hd1 in
              bind uu____4364
                (fun hd2  ->
                   let fa uu____4384 =
                     match uu____4384 with
                     | (a,q) ->
                         let uu____4397 = ff a in
                         bind uu____4397 (fun a1  -> ret (a1, q)) in
                   let uu____4410 = mapM fa args in
                   bind uu____4410
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4470 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4470 with
               | (bs1,t') ->
                   let uu____4479 =
                     let uu____4482 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4482 t' in
                   bind uu____4479
                     (fun t''  ->
                        let uu____4486 =
                          let uu____4487 =
                            let uu____4504 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4505 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4504, uu____4505, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4487 in
                        ret uu____4486))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4526 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___110_4530 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___110_4530.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___110_4530.FStar_Syntax_Syntax.vars)
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
            let uu____4559 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4559 with
            | (t1,lcomp,g) ->
                let uu____4571 =
                  (let uu____4574 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____4574) ||
                    (let uu____4576 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4576) in
                if uu____4571
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4583 = new_uvar env typ in
                   bind uu____4583
                     (fun uu____4599  ->
                        match uu____4599 with
                        | (ut,guard) ->
                            (log ps
                               (fun uu____4612  ->
                                  let uu____4613 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  let uu____4614 =
                                    FStar_Syntax_Print.term_to_string ut in
                                  FStar_Util.print2
                                    "Pointwise_rec: making equality %s = %s\n"
                                    uu____4613 uu____4614);
                             (let uu____4615 =
                                let uu____4618 =
                                  let uu____4619 =
                                    FStar_TypeChecker_TcTerm.universe_of env
                                      typ in
                                  FStar_Syntax_Util.mk_eq2 uu____4619 typ t1
                                    ut in
                                add_irrelevant_goal env uu____4618 opts in
                              bind uu____4615
                                (fun uu____4622  ->
                                   let uu____4623 =
                                     bind tau
                                       (fun uu____4629  ->
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env guard;
                                          (let ut1 =
                                             FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                               env ut in
                                           ret ut1)) in
                                   focus uu____4623)))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4651 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4651 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____4688  ->
                   let uu____4689 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4689);
              bind dismiss_all
                (fun uu____4692  ->
                   let uu____4693 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____4693
                     (fun gt'  ->
                        log ps
                          (fun uu____4703  ->
                             let uu____4704 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4704);
                        (let uu____4705 = push_goals gs in
                         bind uu____4705
                           (fun uu____4709  ->
                              add_goals
                                [(let uu___111_4711 = g in
                                  {
                                    context = (uu___111_4711.context);
                                    witness = (uu___111_4711.witness);
                                    goal_ty = gt';
                                    opts = (uu___111_4711.opts)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4731 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____4731 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4743 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4743 with
            | (hd1,args) ->
                let uu____4776 =
                  let uu____4789 =
                    let uu____4790 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4790.FStar_Syntax_Syntax.n in
                  (uu____4789, args) in
                (match uu____4776 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4804::(l,uu____4806)::(r,uu____4808)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4855 =
                       let uu____4856 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____4856 in
                     if uu____4855
                     then
                       let uu____4859 = FStar_Syntax_Print.term_to_string l in
                       let uu____4860 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4859 uu____4860
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____4864) ->
                     let uu____4881 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____4881))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4889 = new_uvar g.context g.goal_ty in
       bind uu____4889
         (fun uu____4904  ->
            match uu____4904 with
            | (u,u_g) ->
                let g' =
                  let uu___112_4914 = g in
                  {
                    context = (uu___112_4914.context);
                    witness = u;
                    goal_ty = (uu___112_4914.goal_ty);
                    opts = (uu___112_4914.opts)
                  } in
                bind dismiss
                  (fun uu____4917  ->
                     let uu____4918 =
                       let uu____4921 =
                         let uu____4922 =
                           FStar_TypeChecker_TcTerm.universe_of g.context
                             g.goal_ty in
                         FStar_Syntax_Util.mk_eq2 uu____4922 g.goal_ty u
                           g.witness in
                       add_irrelevant_goal g.context uu____4921 g.opts in
                     bind uu____4918
                       (fun uu____4925  ->
                          let uu____4926 = add_goals [g'] in
                          bind uu____4926 (fun uu____4930  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___113_4947 = ps in
              {
                main_context = (uu___113_4947.main_context);
                main_goal = (uu___113_4947.main_goal);
                all_implicits = (uu___113_4947.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___113_4947.smt_goals)
              })
       | uu____4948 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___114_4963 = ps in
              {
                main_context = (uu___114_4963.main_context);
                main_goal = (uu___114_4963.main_goal);
                all_implicits = (uu___114_4963.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___114_4963.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____4970 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____5012 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____5012 with
         | (t1,typ,guard) ->
             let uu____5028 = FStar_Syntax_Util.head_and_args typ in
             (match uu____5028 with
              | (hd1,args) ->
                  let uu____5071 =
                    let uu____5084 =
                      let uu____5085 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____5085.FStar_Syntax_Syntax.n in
                    (uu____5084, args) in
                  (match uu____5071 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____5104)::(q,uu____5106)::[]) when
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
                         let uu___115_5144 = g in
                         let uu____5145 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____5145;
                           witness = (uu___115_5144.witness);
                           goal_ty = (uu___115_5144.goal_ty);
                           opts = (uu___115_5144.opts)
                         } in
                       let g2 =
                         let uu___116_5147 = g in
                         let uu____5148 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____5148;
                           witness = (uu___116_5147.witness);
                           goal_ty = (uu___116_5147.goal_ty);
                           opts = (uu___116_5147.opts)
                         } in
                       bind dismiss
                         (fun uu____5155  ->
                            let uu____5156 = add_goals [g1; g2] in
                            bind uu____5156
                              (fun uu____5165  ->
                                 let uu____5166 =
                                   let uu____5171 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____5172 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____5171, uu____5172) in
                                 ret uu____5166))
                   | uu____5177 ->
                       let uu____5190 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____5190)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5213 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____5213);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___117_5220 = g in
                 {
                   context = (uu___117_5220.context);
                   witness = (uu___117_5220.witness);
                   goal_ty = (uu___117_5220.goal_ty);
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
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (proofstate,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____5256 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5256 with
      | (u,uu____5274,g_u) ->
          let g =
            let uu____5289 = FStar_Options.peek () in
            { context = env; witness = u; goal_ty = typ; opts = uu____5289 } in
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            } in
          (ps, u)