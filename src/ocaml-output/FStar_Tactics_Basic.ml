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
          ("proof-state", uu____606) in
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
      FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
        (msg, ps)
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
      let uu____794 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____794 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____816 =
              let uu____819 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____819 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____816);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail: 'Auu____859 . Prims.string -> 'Auu____859 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____870 =
            FStar_TypeChecker_Env.debug ps.main_context
              (FStar_Options.Other "TacFail") in
          if uu____870
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         Failed (msg, ps))
let fail1: 'Auu____878 . Prims.string -> Prims.string -> 'Auu____878 tac =
  fun msg  ->
    fun x  -> let uu____889 = FStar_Util.format1 msg x in fail uu____889
let fail2:
  'Auu____898 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____898 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____913 = FStar_Util.format2 msg x y in fail uu____913
let fail3:
  'Auu____924 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____924 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____943 = FStar_Util.format3 msg x y z in fail uu____943
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____971 = run t ps in
         match uu____971 with
         | Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              Success ((FStar_Pervasives_Native.Some a), q))
         | Failed (uu____985,uu____986) ->
             (FStar_Syntax_Unionfind.rollback tx;
              Success (FStar_Pervasives_Native.None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____1001  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____1010 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____1010
      then ()
      else
        (let uu____1012 =
           let uu____1013 =
             let uu____1014 = FStar_Syntax_Print.term_to_string solution in
             let uu____1015 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____1016 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____1014
               uu____1015 uu____1016 in
           TacFailure uu____1013 in
         FStar_Exn.raise uu____1012)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____1022 =
         let uu___82_1023 = p in
         let uu____1024 = FStar_List.tl p.goals in
         {
           main_context = (uu___82_1023.main_context);
           main_goal = (uu___82_1023.main_goal);
           all_implicits = (uu___82_1023.all_implicits);
           goals = uu____1024;
           smt_goals = (uu___82_1023.smt_goals)
         } in
       set uu____1022)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___83_1033 = p in
          {
            main_context = (uu___83_1033.main_context);
            main_goal = (uu___83_1033.main_goal);
            all_implicits = (uu___83_1033.all_implicits);
            goals = [];
            smt_goals = (uu___83_1033.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_1050 = p in
            {
              main_context = (uu___84_1050.main_context);
              main_goal = (uu___84_1050.main_goal);
              all_implicits = (uu___84_1050.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___84_1050.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___85_1067 = p in
            {
              main_context = (uu___85_1067.main_context);
              main_goal = (uu___85_1067.main_goal);
              all_implicits = (uu___85_1067.all_implicits);
              goals = (uu___85_1067.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___86_1084 = p in
            {
              main_context = (uu___86_1084.main_context);
              main_goal = (uu___86_1084.main_goal);
              all_implicits = (uu___86_1084.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___86_1084.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___87_1101 = p in
            {
              main_context = (uu___87_1101.main_context);
              main_goal = (uu___87_1101.main_goal);
              all_implicits = (uu___87_1101.all_implicits);
              goals = (uu___87_1101.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1111  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___88_1124 = p in
            {
              main_context = (uu___88_1124.main_context);
              main_goal = (uu___88_1124.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___88_1124.goals);
              smt_goals = (uu___88_1124.smt_goals)
            }))
let new_uvar:
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2 tac
  =
  fun env  ->
    fun typ  ->
      let uu____1157 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____1157 with
      | (u,uu____1177,g_u) ->
          let uu____1191 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____1191 (fun uu____1199  -> ret (u, g_u))
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
          (fun uu____1298  ->
             match uu____1298 with
             | (u,g_u) ->
                 let goal =
                   { context = env; witness = u; goal_ty = typ; opts } in
                 add_goals [goal])
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1313 = is_irrelevant g in
       if uu____1313
       then bind dismiss (fun uu____1317  -> add_smt_goals [g])
       else
         (let uu____1319 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1319))
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
             let uu____1365 =
               try
                 let uu____1399 = FStar_List.splitAt n1 p.goals in
                 ret uu____1399
               with | uu____1429 -> fail "divide: not enough goals" in
             bind uu____1365
               (fun uu____1456  ->
                  match uu____1456 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___89_1482 = p in
                        {
                          main_context = (uu___89_1482.main_context);
                          main_goal = (uu___89_1482.main_goal);
                          all_implicits = (uu___89_1482.all_implicits);
                          goals = lgs;
                          smt_goals = []
                        } in
                      let rp =
                        let uu___90_1484 = p in
                        {
                          main_context = (uu___90_1484.main_context);
                          main_goal = (uu___90_1484.main_goal);
                          all_implicits = (uu___90_1484.all_implicits);
                          goals = rgs;
                          smt_goals = []
                        } in
                      let uu____1485 = set lp in
                      bind uu____1485
                        (fun uu____1493  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1507 = set rp in
                                     bind uu____1507
                                       (fun uu____1515  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___91_1531 = p in
                                                      {
                                                        main_context =
                                                          (uu___91_1531.main_context);
                                                        main_goal =
                                                          (uu___91_1531.main_goal);
                                                        all_implicits =
                                                          (uu___91_1531.all_implicits);
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
                                                    let uu____1532 = set p' in
                                                    bind uu____1532
                                                      (fun uu____1540  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1560 = divide (Prims.parse_int "1") f idtac in
    bind uu____1560
      (fun uu____1573  -> match uu____1573 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.goals with
         | [] -> ret []
         | uu____1608::uu____1609 ->
             let uu____1612 =
               let uu____1621 = map tau in
               divide (Prims.parse_int "1") tau uu____1621 in
             bind uu____1612
               (fun uu____1639  ->
                  match uu____1639 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1678 =
        bind t1
          (fun uu____1683  ->
             let uu____1684 = map t2 in
             bind uu____1684 (fun uu____1692  -> ret ())) in
      focus uu____1678
let intro:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 tac
  =
  bind cur_goal
    (fun goal  ->
       let uu____1715 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1715 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1734 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1734 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1769 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1774 =
                  let uu____1775 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1775 in
                if uu____1774
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1797 = new_uvar env' typ' in
                   bind uu____1797
                     (fun uu____1817  ->
                        match uu____1817 with
                        | (u,g) ->
                            let uu____1830 =
                              let uu____1831 =
                                FStar_Syntax_Util.abs [b1] u
                                  FStar_Pervasives_Native.None in
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                goal.witness uu____1831 in
                            if uu____1830
                            then
                              let uu____1846 =
                                let uu____1849 =
                                  let uu___94_1850 = goal in
                                  let uu____1851 = bnorm env' u in
                                  let uu____1852 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1851;
                                    goal_ty = uu____1852;
                                    opts = (uu___94_1850.opts)
                                  } in
                                replace_cur uu____1849 in
                              bind uu____1846 (fun uu____1858  -> ret b1)
                            else fail "intro: unification failed")))
       | FStar_Pervasives_Native.None  ->
           let uu____1872 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1872)
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
       (let uu____1909 = FStar_Syntax_Util.arrow_one goal.goal_ty in
        match uu____1909 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1932 = FStar_Syntax_Subst.open_comp [b] c in
            (match uu____1932 with
             | (bs,c1) ->
                 let b1 =
                   match bs with
                   | b1::[] -> b1
                   | uu____1971 ->
                       failwith
                         "impossible: open_comp returned different amount of binders" in
                 let uu____1976 =
                   let uu____1977 = FStar_Syntax_Util.is_total_comp c1 in
                   Prims.op_Negation uu____1977 in
                 if uu____1976
                 then fail "Codomain is effectful"
                 else
                   (let bv =
                      FStar_Syntax_Syntax.gen_bv "__recf"
                        FStar_Pervasives_Native.None goal.goal_ty in
                    let bs1 =
                      let uu____2001 = FStar_Syntax_Syntax.mk_binder bv in
                      [uu____2001; b1] in
                    let env' =
                      FStar_TypeChecker_Env.push_binders goal.context bs1 in
                    let uu____2011 =
                      let uu____2018 = comp_to_typ c1 in
                      new_uvar env' uu____2018 in
                    bind uu____2011
                      (fun uu____2043  ->
                         match uu____2043 with
                         | (u,g) ->
                             let lb =
                               let uu____2061 =
                                 FStar_Syntax_Util.abs [b1] u
                                   FStar_Pervasives_Native.None in
                               FStar_Syntax_Util.mk_letbinding
                                 (FStar_Util.Inl bv) [] goal.goal_ty
                                 FStar_Parser_Const.effect_Tot_lid uu____2061 in
                             let body = FStar_Syntax_Syntax.bv_to_name bv in
                             let uu____2073 =
                               FStar_Syntax_Subst.close_let_rec [lb] body in
                             (match uu____2073 with
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
                                      let uu____2119 =
                                        let uu____2122 =
                                          let uu___95_2123 = goal in
                                          let uu____2124 = bnorm env' u in
                                          let uu____2125 =
                                            let uu____2126 = comp_to_typ c1 in
                                            bnorm env' uu____2126 in
                                          {
                                            context = env';
                                            witness = uu____2124;
                                            goal_ty = uu____2125;
                                            opts = (uu___95_2123.opts)
                                          } in
                                        replace_cur uu____2122 in
                                      bind uu____2119
                                        (fun uu____2137  ->
                                           let uu____2138 =
                                             let uu____2147 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 bv in
                                             (uu____2147, b1) in
                                           ret uu____2138)
                                    else fail "intro_rec: unification failed"))))))
        | FStar_Pervasives_Native.None  ->
            let uu____2173 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2173))
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
           let uu____2211 =
             let uu____2214 = FStar_List.map tr s in
             FStar_List.flatten uu____2214 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2211 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___96_2225 = goal in
            {
              context = (uu___96_2225.context);
              witness = w;
              goal_ty = t;
              opts = (uu___96_2225.opts)
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
       let uu____2244 = istrivial goal.context goal.goal_ty in
       if uu____2244
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____2249 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____2249))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2261 =
           try
             let uu____2289 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____2289
           with
           | e ->
               let uu____2316 = FStar_Syntax_Print.term_to_string t in
               let uu____2317 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____2316
                 uu____2317 in
         bind uu____2261
           (fun uu____2335  ->
              match uu____2335 with
              | (t1,typ,guard) ->
                  let uu____2347 =
                    let uu____2348 =
                      let uu____2349 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2349 in
                    Prims.op_Negation uu____2348 in
                  if uu____2347
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2353 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____2353
                     then (solve goal t1; dismiss)
                     else
                       (let uu____2358 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____2359 =
                          let uu____2360 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____2360 in
                        let uu____2361 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2358 uu____2359 uu____2361))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2373 =
           try
             let uu____2401 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____2401
           with
           | e ->
               let uu____2428 = FStar_Syntax_Print.term_to_string t in
               let uu____2429 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2428
                 uu____2429 in
         bind uu____2373
           (fun uu____2447  ->
              match uu____2447 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2465 =
                       let uu____2466 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2466 in
                     if uu____2465
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2470 =
                          let uu____2479 =
                            let uu____2488 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2488.FStar_Syntax_Syntax.effect_args in
                          match uu____2479 with
                          | pre::post::uu____2499 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2540 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2470 with
                        | (pre,post) ->
                            let uu____2569 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____2569
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____2574  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____2576 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____2577 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____2578 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2576 uu____2577 uu____2578)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____2590 =
          let uu____2597 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____2597 in
        FStar_List.map FStar_Pervasives_Native.fst uu____2590 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2635 = let uu____2640 = exact tm in trytac uu____2640 in
           bind uu____2635
             (fun r  ->
                match r with
                | FStar_Pervasives_Native.Some r1 -> ret ()
                | FStar_Pervasives_Native.None  ->
                    let uu____2653 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____2653 with
                     | (tm1,typ,guard) ->
                         let uu____2665 =
                           let uu____2666 =
                             let uu____2667 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____2667 in
                           Prims.op_Negation uu____2666 in
                         if uu____2665
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____2671 = FStar_Syntax_Util.arrow_one typ in
                            match uu____2671 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____2684 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____2684
                            | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                let uu____2700 =
                                  let uu____2701 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2701 in
                                if uu____2700
                                then fail "apply: not total"
                                else
                                  (let uu____2705 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2705
                                     (fun uu____2721  ->
                                        match uu____2721 with
                                        | (u,g_u) ->
                                            let tm' =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                tm1 [(u, aq)]
                                                FStar_Pervasives_Native.None
                                                (goal.context).FStar_TypeChecker_Env.range in
                                            let uu____2741 = __apply uopt tm' in
                                            bind uu____2741
                                              (fun uu____2748  ->
                                                 let uu____2749 =
                                                   let uu____2750 =
                                                     let uu____2753 =
                                                       let uu____2754 =
                                                         FStar_Syntax_Util.head_and_args
                                                           u in
                                                       FStar_Pervasives_Native.fst
                                                         uu____2754 in
                                                     FStar_Syntax_Subst.compress
                                                       uu____2753 in
                                                   uu____2750.FStar_Syntax_Syntax.n in
                                                 match uu____2749 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     (uvar,uu____2782) ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____2810 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____2810
                                                          then ret ()
                                                          else
                                                            (let uu____2814 =
                                                               let uu____2817
                                                                 =
                                                                 let uu____2818
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____2819
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____2818;
                                                                   goal_ty =
                                                                    uu____2819;
                                                                   opts =
                                                                    (goal.opts)
                                                                 } in
                                                               [uu____2817] in
                                                             add_goals
                                                               uu____2814))
                                                 | uu____2820 -> ret ())))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____2829 = __apply true tm in focus uu____2829
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____2847 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____2847 with
         | (tm1,t,guard) ->
             let uu____2859 =
               let uu____2860 =
                 let uu____2861 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____2861 in
               Prims.op_Negation uu____2860 in
             if uu____2859
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____2865 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____2865 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2895 =
                         FStar_List.fold_left
                           (fun uu____2941  ->
                              fun uu____2942  ->
                                match (uu____2941, uu____2942) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____3033 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____3033 with
                                     | (u,uu____3061,g_u) ->
                                         let uu____3075 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____3075,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____2895 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____3133 =
                             let uu____3142 =
                               let uu____3151 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____3151.FStar_Syntax_Syntax.effect_args in
                             match uu____3142 with
                             | pre::post::uu____3162 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____3203 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____3133 with
                            | (pre,post) ->
                                let uu____3232 =
                                  let uu____3235 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____3235 goal.goal_ty in
                                (match uu____3232 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____3238 =
                                       let uu____3239 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____3239 in
                                     let uu____3240 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____3238 uu____3240
                                 | FStar_Pervasives_Native.Some g ->
                                     let uu____3242 =
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
                                            (fun uu____3313  ->
                                               match uu____3313 with
                                               | (uu____3326,uu____3327,uu____3328,tm2,uu____3330,uu____3331)
                                                   ->
                                                   let uu____3332 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____3332 with
                                                    | (hd1,uu____3348) ->
                                                        let uu____3369 =
                                                          let uu____3370 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____3370.FStar_Syntax_Syntax.n in
                                                        (match uu____3369
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____3373 ->
                                                             true
                                                         | uu____3390 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____3400  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____3411 =
                                                 let uu____3418 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____3418 in
                                               FStar_List.map
                                                 FStar_Pervasives_Native.fst
                                                 uu____3411 in
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
                                             let uu____3459 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____3459 with
                                             | (hd1,uu____3475) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____3497) ->
                                                      appears uv goals
                                                  | uu____3522 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____3563  ->
                                                     match uu____3563 with
                                                     | (_msg,_env,_uvar,term,typ,uu____3581)
                                                         ->
                                                         let uu____3582 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____3583 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____3582;
                                                           goal_ty =
                                                             uu____3583;
                                                           opts = (goal.opts)
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____3621 = f x xs1 in
                                                 if uu____3621
                                                 then
                                                   let uu____3624 =
                                                     filter' f xs1 in
                                                   x :: uu____3624
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____3638 =
                                                      checkone g1.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____3638) sub_goals in
                                           let uu____3639 =
                                             add_irrelevant_goal goal.context
                                               pre goal.opts in
                                           bind uu____3639
                                             (fun uu____3644  ->
                                                let uu____3645 =
                                                  trytac trivial in
                                                bind uu____3645
                                                  (fun uu____3654  ->
                                                     let uu____3657 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits in
                                                     bind uu____3657
                                                       (fun uu____3661  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3673 =
           FStar_All.pipe_left mlog
             (fun uu____3683  ->
                let uu____3684 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3685 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3684
                  uu____3685) in
         bind uu____3673
           (fun uu____3697  ->
              let uu____3698 =
                let uu____3701 =
                  let uu____3702 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3702 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____3701 in
              match uu____3698 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                  (l,uu____3714::(x,uu____3716)::(e,uu____3718)::[])) when
                  FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
                  let uu____3765 =
                    let uu____3766 = FStar_Syntax_Subst.compress x in
                    uu____3766.FStar_Syntax_Syntax.n in
                  (match uu____3765 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___101_3773 = goal in
                         let uu____3774 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____3777 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___101_3773.context);
                           witness = uu____3774;
                           goal_ty = uu____3777;
                           opts = (uu___101_3773.opts)
                         } in
                       replace_cur goal1
                   | uu____3780 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3781 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3789 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3789 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let uu____3811 = FStar_Util.set_mem x fns_ty in
           if uu____3811
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____3815 = new_uvar env' goal.goal_ty in
              bind uu____3815
                (fun uu____3830  ->
                   match uu____3830 with
                   | (u,g) ->
                       let uu____3839 =
                         let uu____3840 =
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness u in
                         Prims.op_Negation uu____3840 in
                       if uu____3839
                       then fail "clear: unification failed"
                       else
                         (let new_goal =
                            let uu___102_3845 = goal in
                            let uu____3846 = bnorm env' u in
                            {
                              context = env';
                              witness = uu____3846;
                              goal_ty = (uu___102_3845.goal_ty);
                              opts = (uu___102_3845.opts)
                            } in
                          bind dismiss
                            (fun uu____3848  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3860 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____3860 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3887 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3887 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____3909 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____3909 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___103_3943 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___103_3943.opts)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3955 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____3955 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____3976 = FStar_Syntax_Print.bv_to_string x in
               let uu____3977 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____3976 uu____3977
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____3995 = revert_all_hd xs1 in
        bind uu____3995 (fun uu____3999  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___104_4016 = g in
           {
             context = ctx';
             witness = (uu___104_4016.witness);
             goal_ty = (uu___104_4016.goal_ty);
             opts = (uu___104_4016.opts)
           } in
         bind dismiss (fun uu____4018  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___105_4035 = g in
           {
             context = ctx';
             witness = (uu___105_4035.witness);
             goal_ty = (uu___105_4035.goal_ty);
             opts = (uu___105_4035.opts)
           } in
         bind dismiss (fun uu____4037  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4079 = f x in
          bind uu____4079
            (fun y  ->
               let uu____4087 = mapM f xs in
               bind uu____4087 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4133 = FStar_Syntax_Subst.compress t in
          uu____4133.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4168 = ff hd1 in
              bind uu____4168
                (fun hd2  ->
                   let fa uu____4188 =
                     match uu____4188 with
                     | (a,q) ->
                         let uu____4201 = ff a in
                         bind uu____4201 (fun a1  -> ret (a1, q)) in
                   let uu____4214 = mapM fa args in
                   bind uu____4214
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4274 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4274 with
               | (bs1,t') ->
                   let uu____4283 =
                     let uu____4286 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4286 t' in
                   bind uu____4283
                     (fun t''  ->
                        let uu____4290 =
                          let uu____4291 =
                            let uu____4308 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4309 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4308, uu____4309, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4291 in
                        ret uu____4290))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4330 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___106_4334 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___106_4334.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___106_4334.FStar_Syntax_Syntax.vars)
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
            let uu____4363 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4363 with
            | (t1,lcomp,g) ->
                let uu____4375 =
                  (let uu____4378 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____4378) ||
                    (let uu____4380 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4380) in
                if uu____4375
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4387 = new_uvar env typ in
                   bind uu____4387
                     (fun uu____4403  ->
                        match uu____4403 with
                        | (ut,guard) ->
                            (log ps
                               (fun uu____4416  ->
                                  let uu____4417 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  let uu____4418 =
                                    FStar_Syntax_Print.term_to_string ut in
                                  FStar_Util.print2
                                    "Pointwise_rec: making equality %s = %s\n"
                                    uu____4417 uu____4418);
                             (let uu____4419 =
                                let uu____4422 =
                                  let uu____4423 =
                                    FStar_TypeChecker_TcTerm.universe_of env
                                      typ in
                                  FStar_Syntax_Util.mk_eq2 uu____4423 typ t1
                                    ut in
                                add_irrelevant_goal env uu____4422 opts in
                              bind uu____4419
                                (fun uu____4426  ->
                                   let uu____4427 =
                                     bind tau
                                       (fun uu____4433  ->
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env guard;
                                          (let ut1 =
                                             FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                               env ut in
                                           ret ut1)) in
                                   focus uu____4427)))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4455 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4455 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____4492  ->
                   let uu____4493 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4493);
              bind dismiss_all
                (fun uu____4496  ->
                   let uu____4497 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____4497
                     (fun gt'  ->
                        log ps
                          (fun uu____4507  ->
                             let uu____4508 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4508);
                        (let uu____4509 = push_goals gs in
                         bind uu____4509
                           (fun uu____4513  ->
                              add_goals
                                [(let uu___107_4515 = g in
                                  {
                                    context = (uu___107_4515.context);
                                    witness = (uu___107_4515.witness);
                                    goal_ty = gt';
                                    opts = (uu___107_4515.opts)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4535 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____4535 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4547 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4547 with
            | (hd1,args) ->
                let uu____4580 =
                  let uu____4593 =
                    let uu____4594 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4594.FStar_Syntax_Syntax.n in
                  (uu____4593, args) in
                (match uu____4580 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4608::(l,uu____4610)::(r,uu____4612)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4659 =
                       let uu____4660 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____4660 in
                     if uu____4659
                     then
                       let uu____4663 = FStar_Syntax_Print.term_to_string l in
                       let uu____4664 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4663 uu____4664
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____4668) ->
                     let uu____4685 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____4685))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4693 = new_uvar g.context g.goal_ty in
       bind uu____4693
         (fun uu____4708  ->
            match uu____4708 with
            | (u,u_g) ->
                let g' =
                  let uu___108_4718 = g in
                  {
                    context = (uu___108_4718.context);
                    witness = u;
                    goal_ty = (uu___108_4718.goal_ty);
                    opts = (uu___108_4718.opts)
                  } in
                bind dismiss
                  (fun uu____4721  ->
                     let uu____4722 =
                       let uu____4725 =
                         let uu____4726 =
                           FStar_TypeChecker_TcTerm.universe_of g.context
                             g.goal_ty in
                         FStar_Syntax_Util.mk_eq2 uu____4726 g.goal_ty u
                           g.witness in
                       add_irrelevant_goal g.context uu____4725 g.opts in
                     bind uu____4722
                       (fun uu____4729  ->
                          let uu____4730 = add_goals [g'] in
                          bind uu____4730 (fun uu____4734  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___109_4751 = ps in
              {
                main_context = (uu___109_4751.main_context);
                main_goal = (uu___109_4751.main_goal);
                all_implicits = (uu___109_4751.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___109_4751.smt_goals)
              })
       | uu____4752 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___110_4767 = ps in
              {
                main_context = (uu___110_4767.main_context);
                main_goal = (uu___110_4767.main_goal);
                all_implicits = (uu___110_4767.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___110_4767.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____4774 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____4816 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____4816 with
         | (t1,typ,guard) ->
             let uu____4832 = FStar_Syntax_Util.head_and_args typ in
             (match uu____4832 with
              | (hd1,args) ->
                  let uu____4875 =
                    let uu____4888 =
                      let uu____4889 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____4889.FStar_Syntax_Syntax.n in
                    (uu____4888, args) in
                  (match uu____4875 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____4908)::(q,uu____4910)::[]) when
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
                         let uu___111_4948 = g in
                         let uu____4949 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____4949;
                           witness = (uu___111_4948.witness);
                           goal_ty = (uu___111_4948.goal_ty);
                           opts = (uu___111_4948.opts)
                         } in
                       let g2 =
                         let uu___112_4951 = g in
                         let uu____4952 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____4952;
                           witness = (uu___112_4951.witness);
                           goal_ty = (uu___112_4951.goal_ty);
                           opts = (uu___112_4951.opts)
                         } in
                       bind dismiss
                         (fun uu____4959  ->
                            let uu____4960 = add_goals [g1; g2] in
                            bind uu____4960
                              (fun uu____4969  ->
                                 let uu____4970 =
                                   let uu____4975 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____4976 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____4975, uu____4976) in
                                 ret uu____4970))
                   | uu____4981 ->
                       let uu____4994 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____4994)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5017 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____5017);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___113_5024 = g in
                 {
                   context = (uu___113_5024.context);
                   witness = (uu___113_5024.witness);
                   goal_ty = (uu___113_5024.goal_ty);
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
      let uu____5060 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5060 with
      | (u,uu____5078,g_u) ->
          let g =
            let uu____5093 = FStar_Options.peek () in
            { context = env; witness = u; goal_ty = typ; opts = uu____5093 } in
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            } in
          (ps, u)