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
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____568 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____568);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____571 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____571);
      FStar_List.iter (dump_goal ps) ps.smt_goals
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
      let uu____627 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____627 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____649 =
              let uu____652 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____652 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____649);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail: 'Auu____692 . Prims.string -> 'Auu____692 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____703 =
            FStar_TypeChecker_Env.debug ps.main_context
              (FStar_Options.Other "TacFail") in
          if uu____703
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         Failed (msg, ps))
let fail1: 'Auu____711 . Prims.string -> Prims.string -> 'Auu____711 tac =
  fun msg  ->
    fun x  -> let uu____722 = FStar_Util.format1 msg x in fail uu____722
let fail2:
  'Auu____731 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____731 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____746 = FStar_Util.format2 msg x y in fail uu____746
let fail3:
  'Auu____757 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____757 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____776 = FStar_Util.format3 msg x y z in fail uu____776
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____804 = run t ps in
         match uu____804 with
         | Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              Success ((FStar_Pervasives_Native.Some a), q))
         | Failed (uu____818,uu____819) ->
             (FStar_Syntax_Unionfind.rollback tx;
              Success (FStar_Pervasives_Native.None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____834  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____843 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____843
      then ()
      else
        (let uu____845 =
           let uu____846 =
             let uu____847 = FStar_Syntax_Print.term_to_string solution in
             let uu____848 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____849 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____847
               uu____848 uu____849 in
           TacFailure uu____846 in
         raise uu____845)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____855 =
         let uu___82_856 = p in
         let uu____857 = FStar_List.tl p.goals in
         {
           main_context = (uu___82_856.main_context);
           main_goal = (uu___82_856.main_goal);
           all_implicits = (uu___82_856.all_implicits);
           goals = uu____857;
           smt_goals = (uu___82_856.smt_goals)
         } in
       set uu____855)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___83_866 = p in
          {
            main_context = (uu___83_866.main_context);
            main_goal = (uu___83_866.main_goal);
            all_implicits = (uu___83_866.all_implicits);
            goals = [];
            smt_goals = (uu___83_866.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_883 = p in
            {
              main_context = (uu___84_883.main_context);
              main_goal = (uu___84_883.main_goal);
              all_implicits = (uu___84_883.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___84_883.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___85_900 = p in
            {
              main_context = (uu___85_900.main_context);
              main_goal = (uu___85_900.main_goal);
              all_implicits = (uu___85_900.all_implicits);
              goals = (uu___85_900.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___86_917 = p in
            {
              main_context = (uu___86_917.main_context);
              main_goal = (uu___86_917.main_goal);
              all_implicits = (uu___86_917.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___86_917.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___87_934 = p in
            {
              main_context = (uu___87_934.main_context);
              main_goal = (uu___87_934.main_goal);
              all_implicits = (uu___87_934.all_implicits);
              goals = (uu___87_934.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____944  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___88_957 = p in
            {
              main_context = (uu___88_957.main_context);
              main_goal = (uu___88_957.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___88_957.goals);
              smt_goals = (uu___88_957.smt_goals)
            }))
let new_uvar:
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2 tac
  =
  fun env  ->
    fun typ  ->
      let uu____990 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____990 with
      | (u,uu____1010,g_u) ->
          let uu____1024 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____1024 (fun uu____1032  -> ret (u, g_u))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1041 = FStar_Syntax_Util.un_squash t in
    match uu____1041 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1051 =
          let uu____1052 = FStar_Syntax_Subst.compress t' in
          uu____1052.FStar_Syntax_Syntax.n in
        (match uu____1051 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1056 -> false)
    | uu____1057 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1066 = FStar_Syntax_Util.un_squash t in
    match uu____1066 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1076 =
          let uu____1077 = FStar_Syntax_Subst.compress t' in
          uu____1077.FStar_Syntax_Syntax.n in
        (match uu____1076 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1081 -> false)
    | uu____1082 -> false
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
        let uu____1116 = new_uvar env typ in
        bind uu____1116
          (fun uu____1131  ->
             match uu____1131 with
             | (u,g_u) ->
                 let goal =
                   { context = env; witness = u; goal_ty = typ; opts } in
                 add_goals [goal])
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1146 = is_irrelevant g in
       if uu____1146
       then bind dismiss (fun uu____1150  -> add_smt_goals [g])
       else
         (let uu____1152 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1152))
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
             let uu____1198 =
               try
                 let uu____1232 = FStar_List.splitAt n1 p.goals in
                 ret uu____1232
               with | uu____1262 -> fail "divide: not enough goals" in
             bind uu____1198
               (fun uu____1289  ->
                  match uu____1289 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___89_1315 = p in
                        {
                          main_context = (uu___89_1315.main_context);
                          main_goal = (uu___89_1315.main_goal);
                          all_implicits = (uu___89_1315.all_implicits);
                          goals = lgs;
                          smt_goals = []
                        } in
                      let rp =
                        let uu___90_1317 = p in
                        {
                          main_context = (uu___90_1317.main_context);
                          main_goal = (uu___90_1317.main_goal);
                          all_implicits = (uu___90_1317.all_implicits);
                          goals = rgs;
                          smt_goals = []
                        } in
                      let uu____1318 = set lp in
                      bind uu____1318
                        (fun uu____1326  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1340 = set rp in
                                     bind uu____1340
                                       (fun uu____1348  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___91_1364 = p in
                                                      {
                                                        main_context =
                                                          (uu___91_1364.main_context);
                                                        main_goal =
                                                          (uu___91_1364.main_goal);
                                                        all_implicits =
                                                          (uu___91_1364.all_implicits);
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
                                                    let uu____1365 = set p' in
                                                    bind uu____1365
                                                      (fun uu____1373  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1393 = divide (Prims.parse_int "1") f idtac in
    bind uu____1393
      (fun uu____1406  -> match uu____1406 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.goals with
         | [] -> ret []
         | uu____1441::uu____1442 ->
             let uu____1445 =
               let uu____1454 = map tau in
               divide (Prims.parse_int "1") tau uu____1454 in
             bind uu____1445
               (fun uu____1472  ->
                  match uu____1472 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1511 =
        bind t1
          (fun uu____1516  ->
             let uu____1517 = map t2 in
             bind uu____1517 (fun uu____1525  -> ret ())) in
      focus uu____1511
let intro:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 tac
  =
  bind cur_goal
    (fun goal  ->
       let uu____1548 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1548 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1567 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1567 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1602 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1607 =
                  let uu____1608 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1608 in
                if uu____1607
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1630 = new_uvar env' typ' in
                   bind uu____1630
                     (fun uu____1650  ->
                        match uu____1650 with
                        | (u,g) ->
                            let uu____1663 =
                              let uu____1664 =
                                FStar_Syntax_Util.abs [b1] u
                                  FStar_Pervasives_Native.None in
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                goal.witness uu____1664 in
                            if uu____1663
                            then
                              let uu____1679 =
                                let uu____1682 =
                                  let uu___94_1683 = goal in
                                  let uu____1684 = bnorm env' u in
                                  let uu____1685 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1684;
                                    goal_ty = uu____1685;
                                    opts = (uu___94_1683.opts)
                                  } in
                                replace_cur uu____1682 in
                              bind uu____1679 (fun uu____1691  -> ret b1)
                            else fail "intro: unification failed")))
       | FStar_Pervasives_Native.None  ->
           let uu____1705 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1705)
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
       (let uu____1742 = FStar_Syntax_Util.arrow_one goal.goal_ty in
        match uu____1742 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1765 = FStar_Syntax_Subst.open_comp [b] c in
            (match uu____1765 with
             | (bs,c1) ->
                 let b1 =
                   match bs with
                   | b1::[] -> b1
                   | uu____1804 ->
                       failwith
                         "impossible: open_comp returned different amount of binders" in
                 let uu____1809 =
                   let uu____1810 = FStar_Syntax_Util.is_total_comp c1 in
                   Prims.op_Negation uu____1810 in
                 if uu____1809
                 then fail "Codomain is effectful"
                 else
                   (let bv =
                      FStar_Syntax_Syntax.gen_bv "__recf"
                        FStar_Pervasives_Native.None goal.goal_ty in
                    let bs1 =
                      let uu____1834 = FStar_Syntax_Syntax.mk_binder bv in
                      [uu____1834; b1] in
                    let env' =
                      FStar_TypeChecker_Env.push_binders goal.context bs1 in
                    let uu____1844 =
                      let uu____1851 = comp_to_typ c1 in
                      new_uvar env' uu____1851 in
                    bind uu____1844
                      (fun uu____1876  ->
                         match uu____1876 with
                         | (u,g) ->
                             let lb =
                               let uu____1894 =
                                 FStar_Syntax_Util.abs [b1] u
                                   FStar_Pervasives_Native.None in
                               FStar_Syntax_Util.mk_letbinding
                                 (FStar_Util.Inl bv) [] goal.goal_ty
                                 FStar_Parser_Const.effect_Tot_lid uu____1894 in
                             let body = FStar_Syntax_Syntax.bv_to_name bv in
                             let uu____1906 =
                               FStar_Syntax_Subst.close_let_rec [lb] body in
                             (match uu____1906 with
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
                                      let uu____1952 =
                                        let uu____1955 =
                                          let uu___95_1956 = goal in
                                          let uu____1957 = bnorm env' u in
                                          let uu____1958 =
                                            let uu____1959 = comp_to_typ c1 in
                                            bnorm env' uu____1959 in
                                          {
                                            context = env';
                                            witness = uu____1957;
                                            goal_ty = uu____1958;
                                            opts = (uu___95_1956.opts)
                                          } in
                                        replace_cur uu____1955 in
                                      bind uu____1952
                                        (fun uu____1970  ->
                                           let uu____1971 =
                                             let uu____1980 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 bv in
                                             (uu____1980, b1) in
                                           ret uu____1971)
                                    else fail "intro_rec: unification failed"))))))
        | FStar_Pervasives_Native.None  ->
            let uu____2006 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2006))
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
           let uu____2044 =
             let uu____2047 = FStar_List.map tr s in
             FStar_List.flatten uu____2047 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2044 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___96_2058 = goal in
            {
              context = (uu___96_2058.context);
              witness = w;
              goal_ty = t;
              opts = (uu___96_2058.opts)
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
       let uu____2077 = istrivial goal.context goal.goal_ty in
       if uu____2077
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____2082 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____2082))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2094 =
           try
             let uu____2122 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____2122
           with
           | e ->
               let uu____2149 = FStar_Syntax_Print.term_to_string t in
               let uu____2150 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____2149
                 uu____2150 in
         bind uu____2094
           (fun uu____2168  ->
              match uu____2168 with
              | (t1,typ,guard) ->
                  let uu____2180 =
                    let uu____2181 =
                      let uu____2182 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2182 in
                    Prims.op_Negation uu____2181 in
                  if uu____2180
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2186 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____2186
                     then (solve goal t1; dismiss)
                     else
                       (let uu____2191 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____2192 =
                          let uu____2193 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____2193 in
                        let uu____2194 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2191 uu____2192 uu____2194))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2206 =
           try
             let uu____2234 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____2234
           with
           | e ->
               let uu____2261 = FStar_Syntax_Print.term_to_string t in
               let uu____2262 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2261
                 uu____2262 in
         bind uu____2206
           (fun uu____2280  ->
              match uu____2280 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2298 =
                       let uu____2299 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2299 in
                     if uu____2298
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2303 =
                          let uu____2312 =
                            let uu____2321 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2321.FStar_Syntax_Syntax.effect_args in
                          match uu____2312 with
                          | pre::post::uu____2332 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2373 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2303 with
                        | (pre,post) ->
                            let uu____2402 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____2402
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____2407  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____2409 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____2410 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____2411 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2409 uu____2410 uu____2411)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____2423 =
          let uu____2430 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____2430 in
        FStar_List.map FStar_Pervasives_Native.fst uu____2423 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2468 = let uu____2473 = exact tm in trytac uu____2473 in
           bind uu____2468
             (fun r  ->
                match r with
                | FStar_Pervasives_Native.Some r1 -> ret ()
                | FStar_Pervasives_Native.None  ->
                    let uu____2486 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____2486 with
                     | (tm1,typ,guard) ->
                         let uu____2498 =
                           let uu____2499 =
                             let uu____2500 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____2500 in
                           Prims.op_Negation uu____2499 in
                         if uu____2498
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____2504 = FStar_Syntax_Util.arrow_one typ in
                            match uu____2504 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____2517 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____2517
                            | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                let uu____2533 =
                                  let uu____2534 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2534 in
                                if uu____2533
                                then fail "apply: not total"
                                else
                                  (let uu____2538 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2538
                                     (fun uu____2554  ->
                                        match uu____2554 with
                                        | (u,g_u) ->
                                            let tm' =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                tm1 [(u, aq)]
                                                FStar_Pervasives_Native.None
                                                (goal.context).FStar_TypeChecker_Env.range in
                                            let uu____2574 = __apply uopt tm' in
                                            bind uu____2574
                                              (fun uu____2581  ->
                                                 let uu____2582 =
                                                   let uu____2583 =
                                                     let uu____2586 =
                                                       let uu____2587 =
                                                         FStar_Syntax_Util.head_and_args
                                                           u in
                                                       FStar_Pervasives_Native.fst
                                                         uu____2587 in
                                                     FStar_Syntax_Subst.compress
                                                       uu____2586 in
                                                   uu____2583.FStar_Syntax_Syntax.n in
                                                 match uu____2582 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     (uvar,uu____2615) ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____2643 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____2643
                                                          then ret ()
                                                          else
                                                            (let uu____2647 =
                                                               let uu____2650
                                                                 =
                                                                 let uu____2651
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____2652
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____2651;
                                                                   goal_ty =
                                                                    uu____2652;
                                                                   opts =
                                                                    (goal.opts)
                                                                 } in
                                                               [uu____2650] in
                                                             add_goals
                                                               uu____2647))
                                                 | uu____2653 -> ret ())))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____2662 = __apply true tm in focus uu____2662
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____2680 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____2680 with
         | (tm1,t,guard) ->
             let uu____2692 =
               let uu____2693 =
                 let uu____2694 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____2694 in
               Prims.op_Negation uu____2693 in
             if uu____2692
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____2698 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____2698 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2728 =
                         FStar_List.fold_left
                           (fun uu____2774  ->
                              fun uu____2775  ->
                                match (uu____2774, uu____2775) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2866 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____2866 with
                                     | (u,uu____2894,g_u) ->
                                         let uu____2908 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____2908,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____2728 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____2966 =
                             let uu____2975 =
                               let uu____2984 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____2984.FStar_Syntax_Syntax.effect_args in
                             match uu____2975 with
                             | pre::post::uu____2995 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____3036 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____2966 with
                            | (pre,post) ->
                                let uu____3065 =
                                  let uu____3068 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____3068 goal.goal_ty in
                                (match uu____3065 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____3071 =
                                       let uu____3072 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____3072 in
                                     let uu____3073 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____3071 uu____3073
                                 | FStar_Pervasives_Native.Some g ->
                                     let uu____3075 =
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
                                            (fun uu____3146  ->
                                               match uu____3146 with
                                               | (uu____3159,uu____3160,uu____3161,tm2,uu____3163,uu____3164)
                                                   ->
                                                   let uu____3165 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____3165 with
                                                    | (hd1,uu____3181) ->
                                                        let uu____3202 =
                                                          let uu____3203 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____3203.FStar_Syntax_Syntax.n in
                                                        (match uu____3202
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____3206 ->
                                                             true
                                                         | uu____3223 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____3233  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____3244 =
                                                 let uu____3251 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____3251 in
                                               FStar_List.map
                                                 FStar_Pervasives_Native.fst
                                                 uu____3244 in
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
                                             let uu____3292 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____3292 with
                                             | (hd1,uu____3308) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____3330) ->
                                                      appears uv goals
                                                  | uu____3355 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____3396  ->
                                                     match uu____3396 with
                                                     | (_msg,_env,_uvar,term,typ,uu____3414)
                                                         ->
                                                         let uu____3415 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____3416 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____3415;
                                                           goal_ty =
                                                             uu____3416;
                                                           opts = (goal.opts)
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____3454 = f x xs1 in
                                                 if uu____3454
                                                 then
                                                   let uu____3457 =
                                                     filter' f xs1 in
                                                   x :: uu____3457
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____3471 =
                                                      checkone g1.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____3471) sub_goals in
                                           let uu____3472 =
                                             add_irrelevant_goal goal.context
                                               pre goal.opts in
                                           bind uu____3472
                                             (fun uu____3477  ->
                                                let uu____3478 =
                                                  trytac trivial in
                                                bind uu____3478
                                                  (fun uu____3487  ->
                                                     let uu____3490 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits in
                                                     bind uu____3490
                                                       (fun uu____3494  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3506 =
           FStar_All.pipe_left mlog
             (fun uu____3516  ->
                let uu____3517 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3518 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3517
                  uu____3518) in
         bind uu____3506
           (fun uu____3530  ->
              let uu____3531 =
                let uu____3534 =
                  let uu____3535 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3535 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____3534 in
              match uu____3531 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                  (l,uu____3547::(x,uu____3549)::(e,uu____3551)::[])) when
                  FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
                  let uu____3598 =
                    let uu____3599 = FStar_Syntax_Subst.compress x in
                    uu____3599.FStar_Syntax_Syntax.n in
                  (match uu____3598 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___101_3606 = goal in
                         let uu____3607 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____3610 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___101_3606.context);
                           witness = uu____3607;
                           goal_ty = uu____3610;
                           opts = (uu___101_3606.opts)
                         } in
                       replace_cur goal1
                   | uu____3613 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3614 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3622 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3622 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let uu____3644 = FStar_Util.set_mem x fns_ty in
           if uu____3644
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____3648 = new_uvar env' goal.goal_ty in
              bind uu____3648
                (fun uu____3663  ->
                   match uu____3663 with
                   | (u,g) ->
                       let uu____3672 =
                         let uu____3673 =
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness u in
                         Prims.op_Negation uu____3673 in
                       if uu____3672
                       then fail "clear: unification failed"
                       else
                         (let new_goal =
                            let uu___102_3678 = goal in
                            let uu____3679 = bnorm env' u in
                            {
                              context = env';
                              witness = uu____3679;
                              goal_ty = (uu___102_3678.goal_ty);
                              opts = (uu___102_3678.opts)
                            } in
                          bind dismiss
                            (fun uu____3681  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3693 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____3693 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3720 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3720 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____3742 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____3742 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___103_3776 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___103_3776.opts)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3788 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____3788 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____3809 = FStar_Syntax_Print.bv_to_string x in
               let uu____3810 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____3809 uu____3810
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____3828 = revert_all_hd xs1 in
        bind uu____3828 (fun uu____3832  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___104_3849 = g in
           {
             context = ctx';
             witness = (uu___104_3849.witness);
             goal_ty = (uu___104_3849.goal_ty);
             opts = (uu___104_3849.opts)
           } in
         bind dismiss (fun uu____3851  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___105_3868 = g in
           {
             context = ctx';
             witness = (uu___105_3868.witness);
             goal_ty = (uu___105_3868.goal_ty);
             opts = (uu___105_3868.opts)
           } in
         bind dismiss (fun uu____3870  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3912 = f x in
          bind uu____3912
            (fun y  ->
               let uu____3920 = mapM f xs in
               bind uu____3920 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____3966 = FStar_Syntax_Subst.compress t in
          uu____3966.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4001 = ff hd1 in
              bind uu____4001
                (fun hd2  ->
                   let fa uu____4021 =
                     match uu____4021 with
                     | (a,q) ->
                         let uu____4034 = ff a in
                         bind uu____4034 (fun a1  -> ret (a1, q)) in
                   let uu____4047 = mapM fa args in
                   bind uu____4047
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4107 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4107 with
               | (bs1,t') ->
                   let uu____4116 =
                     let uu____4119 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4119 t' in
                   bind uu____4116
                     (fun t''  ->
                        let uu____4123 =
                          let uu____4124 =
                            let uu____4141 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4142 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4141, uu____4142, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4124 in
                        ret uu____4123))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4163 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___106_4167 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___106_4167.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___106_4167.FStar_Syntax_Syntax.vars)
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
            let uu____4196 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4196 with
            | (t1,lcomp,g) ->
                let uu____4208 =
                  (let uu____4211 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____4211) ||
                    (let uu____4213 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4213) in
                if uu____4208
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4220 = new_uvar env typ in
                   bind uu____4220
                     (fun uu____4236  ->
                        match uu____4236 with
                        | (ut,guard) ->
                            (log ps
                               (fun uu____4249  ->
                                  let uu____4250 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  let uu____4251 =
                                    FStar_Syntax_Print.term_to_string ut in
                                  FStar_Util.print2
                                    "Pointwise_rec: making equality %s = %s\n"
                                    uu____4250 uu____4251);
                             (let uu____4252 =
                                let uu____4255 =
                                  let uu____4256 =
                                    FStar_TypeChecker_TcTerm.universe_of env
                                      typ in
                                  FStar_Syntax_Util.mk_eq2 uu____4256 typ t1
                                    ut in
                                add_irrelevant_goal env uu____4255 opts in
                              bind uu____4252
                                (fun uu____4259  ->
                                   let uu____4260 =
                                     bind tau
                                       (fun uu____4266  ->
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env guard;
                                          (let ut1 =
                                             FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                               env ut in
                                           ret ut1)) in
                                   focus uu____4260)))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4288 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4288 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____4325  ->
                   let uu____4326 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4326);
              bind dismiss_all
                (fun uu____4329  ->
                   let uu____4330 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____4330
                     (fun gt'  ->
                        log ps
                          (fun uu____4340  ->
                             let uu____4341 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4341);
                        (let uu____4342 = push_goals gs in
                         bind uu____4342
                           (fun uu____4346  ->
                              add_goals
                                [(let uu___107_4348 = g in
                                  {
                                    context = (uu___107_4348.context);
                                    witness = (uu___107_4348.witness);
                                    goal_ty = gt';
                                    opts = (uu___107_4348.opts)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4368 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____4368 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4380 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4380 with
            | (hd1,args) ->
                let uu____4413 =
                  let uu____4426 =
                    let uu____4427 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4427.FStar_Syntax_Syntax.n in
                  (uu____4426, args) in
                (match uu____4413 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4441::(l,uu____4443)::(r,uu____4445)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4492 =
                       let uu____4493 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____4493 in
                     if uu____4492
                     then
                       let uu____4496 = FStar_Syntax_Print.term_to_string l in
                       let uu____4497 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4496 uu____4497
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____4501) ->
                     let uu____4518 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____4518))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4526 = new_uvar g.context g.goal_ty in
       bind uu____4526
         (fun uu____4541  ->
            match uu____4541 with
            | (u,u_g) ->
                let g' =
                  let uu___108_4551 = g in
                  {
                    context = (uu___108_4551.context);
                    witness = u;
                    goal_ty = (uu___108_4551.goal_ty);
                    opts = (uu___108_4551.opts)
                  } in
                bind dismiss
                  (fun uu____4554  ->
                     let uu____4555 =
                       let uu____4558 =
                         let uu____4559 =
                           FStar_TypeChecker_TcTerm.universe_of g.context
                             g.goal_ty in
                         FStar_Syntax_Util.mk_eq2 uu____4559 g.goal_ty u
                           g.witness in
                       add_irrelevant_goal g.context uu____4558 g.opts in
                     bind uu____4555
                       (fun uu____4562  ->
                          let uu____4563 = add_goals [g'] in
                          bind uu____4563 (fun uu____4567  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___109_4584 = ps in
              {
                main_context = (uu___109_4584.main_context);
                main_goal = (uu___109_4584.main_goal);
                all_implicits = (uu___109_4584.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___109_4584.smt_goals)
              })
       | uu____4585 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___110_4600 = ps in
              {
                main_context = (uu___110_4600.main_context);
                main_goal = (uu___110_4600.main_goal);
                all_implicits = (uu___110_4600.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___110_4600.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____4607 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____4649 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____4649 with
         | (t1,typ,guard) ->
             let uu____4665 = FStar_Syntax_Util.head_and_args typ in
             (match uu____4665 with
              | (hd1,args) ->
                  let uu____4708 =
                    let uu____4721 =
                      let uu____4722 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____4722.FStar_Syntax_Syntax.n in
                    (uu____4721, args) in
                  (match uu____4708 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____4741)::(q,uu____4743)::[]) when
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
                         let uu___111_4781 = g in
                         let uu____4782 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____4782;
                           witness = (uu___111_4781.witness);
                           goal_ty = (uu___111_4781.goal_ty);
                           opts = (uu___111_4781.opts)
                         } in
                       let g2 =
                         let uu___112_4784 = g in
                         let uu____4785 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____4785;
                           witness = (uu___112_4784.witness);
                           goal_ty = (uu___112_4784.goal_ty);
                           opts = (uu___112_4784.opts)
                         } in
                       bind dismiss
                         (fun uu____4792  ->
                            let uu____4793 = add_goals [g1; g2] in
                            bind uu____4793
                              (fun uu____4802  ->
                                 let uu____4803 =
                                   let uu____4808 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____4809 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____4808, uu____4809) in
                                 ret uu____4803))
                   | uu____4814 ->
                       let uu____4827 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____4827)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____4850 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____4850);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___113_4857 = g in
                 {
                   context = (uu___113_4857.context);
                   witness = (uu___113_4857.witness);
                   goal_ty = (uu___113_4857.goal_ty);
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
      let uu____4893 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____4893 with
      | (u,uu____4911,g_u) ->
          let g =
            let uu____4926 = FStar_Options.peek () in
            { context = env; witness = u; goal_ty = typ; opts = uu____4926 } in
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            } in
          (ps, u)