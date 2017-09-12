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
    let uu____469 = FStar_Syntax_Print.term_to_string g.witness in
    let uu____470 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____469 uu____470
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____483 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____483
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____496 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____496
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____513 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____513
let comp_to_typ: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____519) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____529) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: goal -> Prims.bool =
  fun g  ->
    let uu____543 =
      let uu____548 =
        FStar_TypeChecker_Normalize.unfold_whnf g.context g.goal_ty in
      FStar_Syntax_Util.un_squash uu____548 in
    match uu____543 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____554 -> false
let dump_goal: 'Auu____565 . 'Auu____565 -> goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____575 = goal_to_string goal in tacprint uu____575
let dump_cur: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____585 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____589 = FStar_List.hd ps.goals in dump_goal ps uu____589))
let ps_to_string:
  (Prims.string,proofstate) FStar_Pervasives_Native.tuple2 -> Prims.string =
  fun uu____597  ->
    match uu____597 with
    | (msg,ps) ->
        let uu____604 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
        let uu____605 =
          let uu____606 = FStar_List.map goal_to_string ps.goals in
          FStar_String.concat "\n" uu____606 in
        let uu____609 =
          FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
        let uu____610 =
          let uu____611 = FStar_List.map goal_to_string ps.smt_goals in
          FStar_String.concat "\n" uu____611 in
        FStar_Util.format5
          "State dump (%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s" msg
          uu____604 uu____605 uu____609 uu____610
let goal_to_json: goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____619 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____619 FStar_Syntax_Print.binders_to_json in
    let uu____620 =
      let uu____627 =
        let uu____634 =
          let uu____639 =
            let uu____640 =
              let uu____647 =
                let uu____652 =
                  let uu____653 = FStar_Syntax_Print.term_to_string g.witness in
                  FStar_Util.JsonStr uu____653 in
                ("witness", uu____652) in
              let uu____654 =
                let uu____661 =
                  let uu____666 =
                    let uu____667 =
                      FStar_Syntax_Print.term_to_string g.goal_ty in
                    FStar_Util.JsonStr uu____667 in
                  ("type", uu____666) in
                [uu____661] in
              uu____647 :: uu____654 in
            FStar_Util.JsonAssoc uu____640 in
          ("goal", uu____639) in
        [uu____634] in
      ("hyps", g_binders) :: uu____627 in
    FStar_Util.JsonAssoc uu____620
let ps_to_json:
  (Prims.string,proofstate) FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____699  ->
    match uu____699 with
    | (msg,ps) ->
        let uu____706 =
          let uu____713 =
            let uu____720 =
              let uu____725 =
                let uu____726 = FStar_List.map goal_to_json ps.goals in
                FStar_Util.JsonList uu____726 in
              ("goals", uu____725) in
            let uu____729 =
              let uu____736 =
                let uu____741 =
                  let uu____742 = FStar_List.map goal_to_json ps.smt_goals in
                  FStar_Util.JsonList uu____742 in
                ("smt-goals", uu____741) in
              [uu____736] in
            uu____720 :: uu____729 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____713 in
        FStar_Util.JsonAssoc uu____706
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____771  ->
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
      let uu____831 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____831 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____853 =
              let uu____856 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____856 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____853);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail: 'Auu____896 . Prims.string -> 'Auu____896 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____907 =
            FStar_TypeChecker_Env.debug ps.main_context
              (FStar_Options.Other "TacFail") in
          if uu____907
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         Failed (msg, ps))
let fail1: 'Auu____915 . Prims.string -> Prims.string -> 'Auu____915 tac =
  fun msg  ->
    fun x  -> let uu____926 = FStar_Util.format1 msg x in fail uu____926
let fail2:
  'Auu____935 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____935 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____950 = FStar_Util.format2 msg x y in fail uu____950
let fail3:
  'Auu____961 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____961 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____980 = FStar_Util.format3 msg x y z in fail uu____980
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____1008 = run t ps in
         match uu____1008 with
         | Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              Success ((FStar_Pervasives_Native.Some a), q))
         | Failed (uu____1022,uu____1023) ->
             (FStar_Syntax_Unionfind.rollback tx;
              Success (FStar_Pervasives_Native.None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____1038  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____1047 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____1047
      then ()
      else
        (let uu____1049 =
           let uu____1050 =
             let uu____1051 = FStar_Syntax_Print.term_to_string solution in
             let uu____1052 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____1053 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____1051
               uu____1052 uu____1053 in
           TacFailure uu____1050 in
         FStar_Exn.raise uu____1049)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____1059 =
         let uu___86_1060 = p in
         let uu____1061 = FStar_List.tl p.goals in
         {
           main_context = (uu___86_1060.main_context);
           main_goal = (uu___86_1060.main_goal);
           all_implicits = (uu___86_1060.all_implicits);
           goals = uu____1061;
           smt_goals = (uu___86_1060.smt_goals)
         } in
       set uu____1059)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___87_1070 = p in
          {
            main_context = (uu___87_1070.main_context);
            main_goal = (uu___87_1070.main_goal);
            all_implicits = (uu___87_1070.all_implicits);
            goals = [];
            smt_goals = (uu___87_1070.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___88_1087 = p in
            {
              main_context = (uu___88_1087.main_context);
              main_goal = (uu___88_1087.main_goal);
              all_implicits = (uu___88_1087.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___88_1087.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___89_1104 = p in
            {
              main_context = (uu___89_1104.main_context);
              main_goal = (uu___89_1104.main_goal);
              all_implicits = (uu___89_1104.all_implicits);
              goals = (uu___89_1104.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___90_1121 = p in
            {
              main_context = (uu___90_1121.main_context);
              main_goal = (uu___90_1121.main_goal);
              all_implicits = (uu___90_1121.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___90_1121.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___91_1138 = p in
            {
              main_context = (uu___91_1138.main_context);
              main_goal = (uu___91_1138.main_goal);
              all_implicits = (uu___91_1138.all_implicits);
              goals = (uu___91_1138.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1148  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___92_1161 = p in
            {
              main_context = (uu___92_1161.main_context);
              main_goal = (uu___92_1161.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___92_1161.goals);
              smt_goals = (uu___92_1161.smt_goals)
            }))
let new_uvar: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun typ  ->
      let uu____1186 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____1186 with
      | (u,uu____1202,g_u) ->
          let uu____1216 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____1216 (fun uu____1220  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1225 = FStar_Syntax_Util.un_squash t in
    match uu____1225 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1235 =
          let uu____1236 = FStar_Syntax_Subst.compress t' in
          uu____1236.FStar_Syntax_Syntax.n in
        (match uu____1235 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1240 -> false)
    | uu____1241 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1250 = FStar_Syntax_Util.un_squash t in
    match uu____1250 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1260 =
          let uu____1261 = FStar_Syntax_Subst.compress t' in
          uu____1261.FStar_Syntax_Syntax.n in
        (match uu____1260 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1265 -> false)
    | uu____1266 -> false
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
        let uu____1300 = new_uvar env typ in
        bind uu____1300
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
        let uu____1323 = mk_irrelevant_goal env phi opts in
        bind uu____1323 (fun goal  -> add_goals [goal])
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
       let uu____1346 = istrivial goal.context goal.goal_ty in
       if uu____1346
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____1351 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1351))
let add_goal_from_guard:
  env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Options.optionstate -> Prims.unit tac
  =
  fun e  ->
    fun g  ->
      fun opts  ->
        let uu____1368 =
          let uu____1369 = FStar_TypeChecker_Rel.simplify_guard e g in
          uu____1369.FStar_TypeChecker_Env.guard_f in
        match uu____1368 with
        | FStar_TypeChecker_Common.Trivial  -> ret ()
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____1373 = istrivial e f in
            if uu____1373
            then ret ()
            else
              (let uu____1377 = mk_irrelevant_goal e f opts in
               bind uu____1377
                 (fun goal  ->
                    let goal1 =
                      let uu___93_1384 = goal in
                      {
                        context = (uu___93_1384.context);
                        witness = (uu___93_1384.witness);
                        goal_ty = (uu___93_1384.goal_ty);
                        opts = (uu___93_1384.opts);
                        is_guard = true
                      } in
                    push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1390 = is_irrelevant g in
       if uu____1390
       then bind dismiss (fun uu____1394  -> add_smt_goals [g])
       else
         (let uu____1396 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1396))
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
             let uu____1442 =
               try
                 let uu____1476 = FStar_List.splitAt n1 p.goals in
                 ret uu____1476
               with | uu____1506 -> fail "divide: not enough goals" in
             bind uu____1442
               (fun uu____1533  ->
                  match uu____1533 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___94_1559 = p in
                        {
                          main_context = (uu___94_1559.main_context);
                          main_goal = (uu___94_1559.main_goal);
                          all_implicits = (uu___94_1559.all_implicits);
                          goals = lgs;
                          smt_goals = []
                        } in
                      let rp =
                        let uu___95_1561 = p in
                        {
                          main_context = (uu___95_1561.main_context);
                          main_goal = (uu___95_1561.main_goal);
                          all_implicits = (uu___95_1561.all_implicits);
                          goals = rgs;
                          smt_goals = []
                        } in
                      let uu____1562 = set lp in
                      bind uu____1562
                        (fun uu____1570  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1584 = set rp in
                                     bind uu____1584
                                       (fun uu____1592  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___96_1608 = p in
                                                      {
                                                        main_context =
                                                          (uu___96_1608.main_context);
                                                        main_goal =
                                                          (uu___96_1608.main_goal);
                                                        all_implicits =
                                                          (uu___96_1608.all_implicits);
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
                                                    let uu____1609 = set p' in
                                                    bind uu____1609
                                                      (fun uu____1617  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1637 = divide (Prims.parse_int "1") f idtac in
    bind uu____1637
      (fun uu____1650  -> match uu____1650 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.goals with
         | [] -> ret []
         | uu____1685::uu____1686 ->
             let uu____1689 =
               let uu____1698 = map tau in
               divide (Prims.parse_int "1") tau uu____1698 in
             bind uu____1689
               (fun uu____1716  ->
                  match uu____1716 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1755 =
        bind t1
          (fun uu____1760  ->
             let uu____1761 = map t2 in
             bind uu____1761 (fun uu____1769  -> ret ())) in
      focus uu____1755
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1780 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1780 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1795 =
             let uu____1796 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1796 in
           if uu____1795
           then fail "Codomain is effectful"
           else
             (let env' = FStar_TypeChecker_Env.push_binders goal.context [b] in
              let typ' = comp_to_typ c in
              let uu____1802 = new_uvar env' typ' in
              bind uu____1802
                (fun u  ->
                   let uu____1809 =
                     let uu____1810 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     FStar_TypeChecker_Rel.teq_nosmt goal.context
                       goal.witness uu____1810 in
                   if uu____1809
                   then
                     let uu____1813 =
                       let uu____1816 =
                         let uu___99_1817 = goal in
                         let uu____1818 = bnorm env' u in
                         let uu____1819 = bnorm env' typ' in
                         {
                           context = env';
                           witness = uu____1818;
                           goal_ty = uu____1819;
                           opts = (uu___99_1817.opts);
                           is_guard = (uu___99_1817.is_guard)
                         } in
                       replace_cur uu____1816 in
                     bind uu____1813 (fun uu____1821  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1827 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1827)
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
       (let uu____1848 = FStar_Syntax_Util.arrow_one goal.goal_ty in
        match uu____1848 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1867 =
              let uu____1868 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1868 in
            if uu____1867
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None goal.goal_ty in
               let bs =
                 let uu____1884 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1884; b] in
               let env' = FStar_TypeChecker_Env.push_binders goal.context bs in
               let uu____1886 =
                 let uu____1889 = comp_to_typ c in new_uvar env' uu____1889 in
               bind uu____1886
                 (fun u  ->
                    let lb =
                      let uu____1906 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.goal_ty FStar_Parser_Const.effect_Tot_lid
                        uu____1906 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1910 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1910 with
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
                            let uu____1948 =
                              let uu____1951 =
                                let uu___100_1952 = goal in
                                let uu____1953 = bnorm env' u in
                                let uu____1954 =
                                  let uu____1955 = comp_to_typ c in
                                  bnorm env' uu____1955 in
                                {
                                  context = env';
                                  witness = uu____1953;
                                  goal_ty = uu____1954;
                                  opts = (uu___100_1952.opts);
                                  is_guard = (uu___100_1952.is_guard)
                                } in
                              replace_cur uu____1951 in
                            bind uu____1948
                              (fun uu____1962  ->
                                 let uu____1963 =
                                   let uu____1968 =
                                     FStar_Syntax_Syntax.mk_binder bv in
                                   (uu____1968, b) in
                                 ret uu____1963)
                          else fail "intro_rec: unification failed"))))
        | FStar_Pervasives_Native.None  ->
            let uu____1982 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1982))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2007 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2007 in
         let w = normalize steps goal.context goal.witness in
         let t = normalize steps goal.context goal.goal_ty in
         replace_cur
           (let uu___101_2014 = goal in
            {
              context = (uu___101_2014.context);
              witness = w;
              goal_ty = t;
              opts = (uu___101_2014.opts);
              is_guard = (uu___101_2014.is_guard)
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
             let uu____2038 = FStar_TypeChecker_Normalize.tr_norm_steps s in
             FStar_List.append
               [FStar_TypeChecker_Normalize.Reify;
               FStar_TypeChecker_Normalize.UnfoldTac] uu____2038 in
           let t1 = normalize steps ps.main_context t in ret t1)
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2053 =
           try
             let uu____2081 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____2081
           with
           | e ->
               let uu____2108 = FStar_Syntax_Print.term_to_string t in
               let uu____2109 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____2108
                 uu____2109 in
         bind uu____2053
           (fun uu____2127  ->
              match uu____2127 with
              | (t1,typ,guard) ->
                  let uu____2139 =
                    let uu____2140 =
                      let uu____2141 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2141 in
                    Prims.op_Negation uu____2140 in
                  if uu____2139
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2145 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____2145
                     then (solve goal t1; dismiss)
                     else
                       (let uu____2150 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____2151 =
                          let uu____2152 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____2152 in
                        let uu____2153 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2150 uu____2151 uu____2153))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  -> let uu____2162 = __exact t in focus uu____2162
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2176 =
           try
             let uu____2204 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____2204
           with
           | e ->
               let uu____2231 = FStar_Syntax_Print.term_to_string t in
               let uu____2232 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2231
                 uu____2232 in
         bind uu____2176
           (fun uu____2250  ->
              match uu____2250 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2268 =
                       let uu____2269 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2269 in
                     if uu____2268
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2273 =
                          let uu____2282 =
                            let uu____2291 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2291.FStar_Syntax_Syntax.effect_args in
                          match uu____2282 with
                          | pre::post::uu____2302 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2343 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2273 with
                        | (pre,post) ->
                            let uu____2372 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____2372
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____2377  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____2379 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____2380 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____2381 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2379 uu____2380 uu____2381)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.is_guard
      then false
      else
        (let free_uvars =
           let uu____2394 =
             let uu____2401 = FStar_Syntax_Free.uvars g.goal_ty in
             FStar_Util.set_elements uu____2401 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2394 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2428 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2448 =
               let uu____2453 = __exact tm in trytac uu____2453 in
             bind uu____2448
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2466 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2466 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           let uu____2496 =
                             let uu____2497 =
                               FStar_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu____2497 in
                           if uu____2496
                           then fail "apply: not total codomain"
                           else
                             (let uu____2501 =
                                new_uvar goal.context
                                  bv.FStar_Syntax_Syntax.sort in
                              bind uu____2501
                                (fun u  ->
                                   let tm' =
                                     FStar_Syntax_Syntax.mk_Tm_app tm
                                       [(u, aq)] FStar_Pervasives_Native.None
                                       (goal.context).FStar_TypeChecker_Env.range in
                                   let typ' =
                                     let uu____2521 = comp_to_typ c in
                                     FStar_All.pipe_left
                                       (FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.NT (bv, u)])
                                       uu____2521 in
                                   let uu____2522 = __apply uopt tm' typ' in
                                   bind uu____2522
                                     (fun uu____2529  ->
                                        let uu____2530 =
                                          let uu____2531 =
                                            let uu____2534 =
                                              let uu____2535 =
                                                FStar_Syntax_Util.head_and_args
                                                  u in
                                              FStar_Pervasives_Native.fst
                                                uu____2535 in
                                            FStar_Syntax_Subst.compress
                                              uu____2534 in
                                          uu____2531.FStar_Syntax_Syntax.n in
                                        match uu____2530 with
                                        | FStar_Syntax_Syntax.Tm_uvar
                                            (uvar,uu____2563) ->
                                            bind get
                                              (fun ps  ->
                                                 let uu____2591 =
                                                   uopt &&
                                                     (uvar_free uvar ps) in
                                                 if uu____2591
                                                 then ret ()
                                                 else
                                                   (let uu____2595 =
                                                      let uu____2598 =
                                                        let uu___106_2599 =
                                                          goal in
                                                        let uu____2600 =
                                                          bnorm goal.context
                                                            u in
                                                        let uu____2601 =
                                                          bnorm goal.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          context =
                                                            (uu___106_2599.context);
                                                          witness =
                                                            uu____2600;
                                                          goal_ty =
                                                            uu____2601;
                                                          opts =
                                                            (uu___106_2599.opts);
                                                          is_guard = false
                                                        } in
                                                      [uu____2598] in
                                                    add_goals uu____2595))
                                        | uu____2602 -> ret ()))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2660 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____2660 with
           | (tm1,typ,guard) ->
               let uu____2672 =
                 let uu____2675 =
                   let uu____2678 = __apply uopt tm1 typ in
                   bind uu____2678
                     (fun uu____2682  ->
                        add_goal_from_guard goal.context guard goal.opts) in
                 focus uu____2675 in
               let uu____2683 =
                 let uu____2686 = FStar_Syntax_Print.term_to_string tm1 in
                 let uu____2687 = FStar_Syntax_Print.term_to_string typ in
                 let uu____2688 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 fail3
                   "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                   uu____2686 uu____2687 uu____2688 in
               try_unif uu____2672 uu____2683)
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2697 =
      let is_unit_t t =
        let uu____2704 =
          let uu____2705 = FStar_Syntax_Subst.compress t in
          uu____2705.FStar_Syntax_Syntax.n in
        match uu____2704 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
            true
        | uu____2709 -> false in
      bind cur_goal
        (fun goal  ->
           let uu____2719 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____2719 with
           | (tm1,t,guard) ->
               let uu____2731 = FStar_Syntax_Util.arrow_formals_comp t in
               (match uu____2731 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2761 =
                         FStar_List.fold_left
                           (fun uu____2807  ->
                              fun uu____2808  ->
                                match (uu____2807, uu____2808) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2911 = is_unit_t b_t in
                                    if uu____2911
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____2949 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.context b_t in
                                       match uu____2949 with
                                       | (u,uu____2979,g_u) ->
                                           let uu____2993 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____2993,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2761 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____3063 =
                             let uu____3072 =
                               let uu____3081 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____3081.FStar_Syntax_Syntax.effect_args in
                             match uu____3072 with
                             | pre::post::uu____3092 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____3133 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____3063 with
                            | (pre,post) ->
                                let uu____3162 =
                                  let uu____3165 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____3165 goal.goal_ty in
                                (match uu____3162 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____3168 =
                                       let uu____3169 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____3169 in
                                     let uu____3170 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____3168 uu____3170
                                 | FStar_Pervasives_Native.Some g ->
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____3242  ->
                                               match uu____3242 with
                                               | (uu____3255,uu____3256,uu____3257,tm2,uu____3259,uu____3260)
                                                   ->
                                                   let uu____3261 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____3261 with
                                                    | (hd1,uu____3277) ->
                                                        let uu____3298 =
                                                          let uu____3299 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____3299.FStar_Syntax_Syntax.n in
                                                        (match uu____3298
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____3302 ->
                                                             true
                                                         | uu____3319 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let uu____3321 =
                                         add_implicits implicits1 in
                                       bind uu____3321
                                         (fun uu____3325  ->
                                            bind dismiss
                                              (fun uu____3334  ->
                                                 let is_free_uvar uv t1 =
                                                   let free_uvars =
                                                     let uu____3345 =
                                                       let uu____3352 =
                                                         FStar_Syntax_Free.uvars
                                                           t1 in
                                                       FStar_Util.set_elements
                                                         uu____3352 in
                                                     FStar_List.map
                                                       FStar_Pervasives_Native.fst
                                                       uu____3345 in
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
                                                   let uu____3393 =
                                                     FStar_Syntax_Util.head_and_args
                                                       t1 in
                                                   match uu____3393 with
                                                   | (hd1,uu____3409) ->
                                                       (match hd1.FStar_Syntax_Syntax.n
                                                        with
                                                        | FStar_Syntax_Syntax.Tm_uvar
                                                            (uv,uu____3431)
                                                            ->
                                                            appears uv goals
                                                        | uu____3456 -> false) in
                                                 let sub_goals =
                                                   FStar_All.pipe_right
                                                     implicits1
                                                     (FStar_List.map
                                                        (fun uu____3498  ->
                                                           match uu____3498
                                                           with
                                                           | (_msg,_env,_uvar,term,typ,uu____3516)
                                                               ->
                                                               let uu___109_3517
                                                                 = goal in
                                                               let uu____3518
                                                                 =
                                                                 bnorm
                                                                   goal.context
                                                                   term in
                                                               let uu____3519
                                                                 =
                                                                 bnorm
                                                                   goal.context
                                                                   typ in
                                                               {
                                                                 context =
                                                                   (uu___109_3517.context);
                                                                 witness =
                                                                   uu____3518;
                                                                 goal_ty =
                                                                   uu____3519;
                                                                 opts =
                                                                   (uu___109_3517.opts);
                                                                 is_guard =
                                                                   (uu___109_3517.is_guard)
                                                               })) in
                                                 let rec filter' f xs =
                                                   match xs with
                                                   | [] -> []
                                                   | x::xs1 ->
                                                       let uu____3557 =
                                                         f x xs1 in
                                                       if uu____3557
                                                       then
                                                         let uu____3560 =
                                                           filter' f xs1 in
                                                         x :: uu____3560
                                                       else filter' f xs1 in
                                                 let sub_goals1 =
                                                   filter'
                                                     (fun g1  ->
                                                        fun goals  ->
                                                          let uu____3574 =
                                                            checkone
                                                              g1.witness
                                                              goals in
                                                          Prims.op_Negation
                                                            uu____3574)
                                                     sub_goals in
                                                 let uu____3575 =
                                                   add_goal_from_guard
                                                     goal.context guard
                                                     goal.opts in
                                                 bind uu____3575
                                                   (fun uu____3580  ->
                                                      let uu____3581 =
                                                        add_goal_from_guard
                                                          goal.context g
                                                          goal.opts in
                                                      bind uu____3581
                                                        (fun uu____3586  ->
                                                           let uu____3587 =
                                                             add_irrelevant_goal
                                                               goal.context
                                                               pre goal.opts in
                                                           bind uu____3587
                                                             (fun uu____3592 
                                                                ->
                                                                let uu____3593
                                                                  =
                                                                  trytac
                                                                    trivial in
                                                                bind
                                                                  uu____3593
                                                                  (fun
                                                                    uu____3601
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))) in
    focus uu____2697
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3620 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3620 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3630::(e1,uu____3632)::(e2,uu____3634)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3693 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3716 = destruct_eq' typ in
    match uu____3716 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3746 = FStar_Syntax_Util.un_squash typ in
        (match uu____3746 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3779 =
           FStar_All.pipe_left mlog
             (fun uu____3789  ->
                let uu____3790 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3791 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3790
                  uu____3791) in
         bind uu____3779
           (fun uu____3799  ->
              let uu____3800 =
                let uu____3807 =
                  let uu____3808 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3808 in
                destruct_eq uu____3807 in
              match uu____3800 with
              | FStar_Pervasives_Native.Some (x,e) ->
                  let uu____3825 =
                    let uu____3826 = FStar_Syntax_Subst.compress x in
                    uu____3826.FStar_Syntax_Syntax.n in
                  (match uu____3825 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___110_3833 = goal in
                         let uu____3834 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____3835 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___110_3833.context);
                           witness = uu____3834;
                           goal_ty = uu____3835;
                           opts = (uu___110_3833.opts);
                           is_guard = (uu___110_3833.is_guard)
                         } in
                       replace_cur goal1
                   | uu____3836 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3837 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3849 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3849 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let uu____3871 = FStar_Util.set_mem x fns_ty in
           if uu____3871
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____3875 = new_uvar env' goal.goal_ty in
              bind uu____3875
                (fun u  ->
                   let uu____3881 =
                     let uu____3882 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context
                         goal.witness u in
                     Prims.op_Negation uu____3882 in
                   if uu____3881
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___111_3887 = goal in
                        let uu____3888 = bnorm env' u in
                        {
                          context = env';
                          witness = uu____3888;
                          goal_ty = (uu___111_3887.goal_ty);
                          opts = (uu___111_3887.opts);
                          is_guard = (uu___111_3887.is_guard)
                        } in
                      bind dismiss (fun uu____3890  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3902 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____3902 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3929 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3929 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____3951 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____3951 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___112_3985 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___112_3985.opts);
                is_guard = (uu___112_3985.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3997 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____3997 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4018 = FStar_Syntax_Print.bv_to_string x in
               let uu____4019 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4018 uu____4019
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____4037 = revert_all_hd xs1 in
        bind uu____4037 (fun uu____4041  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___113_4058 = g in
           {
             context = ctx';
             witness = (uu___113_4058.witness);
             goal_ty = (uu___113_4058.goal_ty);
             opts = (uu___113_4058.opts);
             is_guard = (uu___113_4058.is_guard)
           } in
         bind dismiss (fun uu____4060  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___114_4077 = g in
           {
             context = ctx';
             witness = (uu___114_4077.witness);
             goal_ty = (uu___114_4077.goal_ty);
             opts = (uu___114_4077.opts);
             is_guard = (uu___114_4077.is_guard)
           } in
         bind dismiss (fun uu____4079  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4121 = f x in
          bind uu____4121
            (fun y  ->
               let uu____4129 = mapM f xs in
               bind uu____4129 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4175 = FStar_Syntax_Subst.compress t in
          uu____4175.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4210 = ff hd1 in
              bind uu____4210
                (fun hd2  ->
                   let fa uu____4230 =
                     match uu____4230 with
                     | (a,q) ->
                         let uu____4243 = ff a in
                         bind uu____4243 (fun a1  -> ret (a1, q)) in
                   let uu____4256 = mapM fa args in
                   bind uu____4256
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4316 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4316 with
               | (bs1,t') ->
                   let uu____4325 =
                     let uu____4328 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4328 t' in
                   bind uu____4325
                     (fun t''  ->
                        let uu____4332 =
                          let uu____4333 =
                            let uu____4350 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4351 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4350, uu____4351, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4333 in
                        ret uu____4332))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4372 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___115_4376 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___115_4376.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___115_4376.FStar_Syntax_Syntax.vars)
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
            let uu____4405 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4405 with
            | (t1,lcomp,g) ->
                let uu____4417 =
                  (let uu____4420 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____4420) ||
                    (let uu____4422 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4422) in
                if uu____4417
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4429 = new_uvar env typ in
                   bind uu____4429
                     (fun ut  ->
                        log ps
                          (fun uu____4440  ->
                             let uu____4441 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4442 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4441 uu____4442);
                        (let uu____4443 =
                           let uu____4446 =
                             let uu____4447 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4447 typ t1 ut in
                           add_irrelevant_goal env uu____4446 opts in
                         bind uu____4443
                           (fun uu____4450  ->
                              let uu____4451 =
                                bind tau
                                  (fun uu____4456  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4451))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4477 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4477 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____4514  ->
                   let uu____4515 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4515);
              bind dismiss_all
                (fun uu____4518  ->
                   let uu____4519 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____4519
                     (fun gt'  ->
                        log ps
                          (fun uu____4529  ->
                             let uu____4530 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4530);
                        (let uu____4531 = push_goals gs in
                         bind uu____4531
                           (fun uu____4535  ->
                              add_goals
                                [(let uu___116_4537 = g in
                                  {
                                    context = (uu___116_4537.context);
                                    witness = (uu___116_4537.witness);
                                    goal_ty = gt';
                                    opts = (uu___116_4537.opts);
                                    is_guard = (uu___116_4537.is_guard)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4557 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____4557 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4569 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4569 with
            | (hd1,args) ->
                let uu____4602 =
                  let uu____4615 =
                    let uu____4616 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4616.FStar_Syntax_Syntax.n in
                  (uu____4615, args) in
                (match uu____4602 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4630::(l,uu____4632)::(r,uu____4634)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4681 =
                       let uu____4682 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____4682 in
                     if uu____4681
                     then
                       let uu____4685 = FStar_Syntax_Print.term_to_string l in
                       let uu____4686 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4685 uu____4686
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____4690) ->
                     let uu____4707 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____4707))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4715 = new_uvar g.context g.goal_ty in
       bind uu____4715
         (fun u  ->
            let g' =
              let uu___117_4722 = g in
              {
                context = (uu___117_4722.context);
                witness = u;
                goal_ty = (uu___117_4722.goal_ty);
                opts = (uu___117_4722.opts);
                is_guard = (uu___117_4722.is_guard)
              } in
            bind dismiss
              (fun uu____4725  ->
                 let uu____4726 =
                   let uu____4729 =
                     let uu____4730 =
                       FStar_TypeChecker_TcTerm.universe_of g.context
                         g.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4730 g.goal_ty u
                       g.witness in
                   add_irrelevant_goal g.context uu____4729 g.opts in
                 bind uu____4726
                   (fun uu____4733  ->
                      let uu____4734 = add_goals [g'] in
                      bind uu____4734 (fun uu____4738  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___118_4755 = ps in
              {
                main_context = (uu___118_4755.main_context);
                main_goal = (uu___118_4755.main_goal);
                all_implicits = (uu___118_4755.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___118_4755.smt_goals)
              })
       | uu____4756 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___119_4771 = ps in
              {
                main_context = (uu___119_4771.main_context);
                main_goal = (uu___119_4771.main_goal);
                all_implicits = (uu___119_4771.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___119_4771.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____4778 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____4820 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____4820 with
         | (t1,typ,guard) ->
             let uu____4836 = FStar_Syntax_Util.head_and_args typ in
             (match uu____4836 with
              | (hd1,args) ->
                  let uu____4879 =
                    let uu____4892 =
                      let uu____4893 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____4893.FStar_Syntax_Syntax.n in
                    (uu____4892, args) in
                  (match uu____4879 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____4912)::(q,uu____4914)::[]) when
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
                         let uu___120_4952 = g in
                         let uu____4953 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____4953;
                           witness = (uu___120_4952.witness);
                           goal_ty = (uu___120_4952.goal_ty);
                           opts = (uu___120_4952.opts);
                           is_guard = (uu___120_4952.is_guard)
                         } in
                       let g2 =
                         let uu___121_4955 = g in
                         let uu____4956 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____4956;
                           witness = (uu___121_4955.witness);
                           goal_ty = (uu___121_4955.goal_ty);
                           opts = (uu___121_4955.opts);
                           is_guard = (uu___121_4955.is_guard)
                         } in
                       bind dismiss
                         (fun uu____4963  ->
                            let uu____4964 = add_goals [g1; g2] in
                            bind uu____4964
                              (fun uu____4973  ->
                                 let uu____4974 =
                                   let uu____4979 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____4980 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____4979, uu____4980) in
                                 ret uu____4974))
                   | uu____4985 ->
                       let uu____4998 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____4998)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5021 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____5021);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___122_5028 = g in
                 {
                   context = (uu___122_5028.context);
                   witness = (uu___122_5028.witness);
                   goal_ty = (uu___122_5028.goal_ty);
                   opts = opts';
                   is_guard = (uu___122_5028.is_guard)
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
           let uu____5069 =
             (goal.context).FStar_TypeChecker_Env.type_of env tm in
           match uu____5069 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5098 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5104 =
              let uu____5105 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5105 in
            new_uvar env uu____5104 in
      bind uu____5098
        (fun typ  ->
           let uu____5117 = new_uvar env typ in
           bind uu____5117 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5137 =
             FStar_TypeChecker_Rel.teq_nosmt ps.main_context t1 t2 in
           ret uu____5137)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5157  ->
             let uu____5158 = FStar_Options.unsafe_tactic_exec () in
             if uu____5158
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5164  -> fun uu____5165  -> false) in
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
      let uu____5187 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5187 with
      | (u,uu____5205,g_u) ->
          let g =
            let uu____5220 = FStar_Options.peek () in
            {
              context = env;
              witness = u;
              goal_ty = typ;
              opts = uu____5220;
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
      let uu____5237 = goal_of_goal_ty env typ in
      match uu____5237 with
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