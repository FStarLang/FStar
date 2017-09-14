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
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____1049 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____1049
      then ()
      else
        (let uu____1051 =
           let uu____1052 =
             let uu____1053 = FStar_Syntax_Print.term_to_string solution in
             let uu____1054 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____1055 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____1053
               uu____1054 uu____1055 in
           TacFailure uu____1052 in
         FStar_Exn.raise uu____1051)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____1061 =
         let uu___86_1062 = p in
         let uu____1063 = FStar_List.tl p.goals in
         {
           main_context = (uu___86_1062.main_context);
           main_goal = (uu___86_1062.main_goal);
           all_implicits = (uu___86_1062.all_implicits);
           goals = uu____1063;
           smt_goals = (uu___86_1062.smt_goals)
         } in
       set uu____1061)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___87_1072 = p in
          {
            main_context = (uu___87_1072.main_context);
            main_goal = (uu___87_1072.main_goal);
            all_implicits = (uu___87_1072.all_implicits);
            goals = [];
            smt_goals = (uu___87_1072.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___88_1089 = p in
            {
              main_context = (uu___88_1089.main_context);
              main_goal = (uu___88_1089.main_goal);
              all_implicits = (uu___88_1089.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___88_1089.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___89_1106 = p in
            {
              main_context = (uu___89_1106.main_context);
              main_goal = (uu___89_1106.main_goal);
              all_implicits = (uu___89_1106.all_implicits);
              goals = (uu___89_1106.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___90_1123 = p in
            {
              main_context = (uu___90_1123.main_context);
              main_goal = (uu___90_1123.main_goal);
              all_implicits = (uu___90_1123.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___90_1123.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___91_1140 = p in
            {
              main_context = (uu___91_1140.main_context);
              main_goal = (uu___91_1140.main_goal);
              all_implicits = (uu___91_1140.all_implicits);
              goals = (uu___91_1140.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1150  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___92_1163 = p in
            {
              main_context = (uu___92_1163.main_context);
              main_goal = (uu___92_1163.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___92_1163.goals);
              smt_goals = (uu___92_1163.smt_goals)
            }))
let new_uvar: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun typ  ->
      let uu____1188 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____1188 with
      | (u,uu____1204,g_u) ->
          let uu____1218 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____1218 (fun uu____1222  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1227 = FStar_Syntax_Util.un_squash t in
    match uu____1227 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1237 =
          let uu____1238 = FStar_Syntax_Subst.compress t' in
          uu____1238.FStar_Syntax_Syntax.n in
        (match uu____1237 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1242 -> false)
    | uu____1243 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1252 = FStar_Syntax_Util.un_squash t in
    match uu____1252 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1262 =
          let uu____1263 = FStar_Syntax_Subst.compress t' in
          uu____1263.FStar_Syntax_Syntax.n in
        (match uu____1262 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1267 -> false)
    | uu____1268 -> false
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
        let uu____1302 = new_uvar env typ in
        bind uu____1302
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
        let uu____1325 = mk_irrelevant_goal env phi opts in
        bind uu____1325 (fun goal  -> add_goals [goal])
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
       let uu____1348 = istrivial goal.context goal.goal_ty in
       if uu____1348
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____1353 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1353))
let add_goal_from_guard:
  env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Options.optionstate -> Prims.unit tac
  =
  fun e  ->
    fun g  ->
      fun opts  ->
        let uu____1370 =
          let uu____1371 = FStar_TypeChecker_Rel.simplify_guard e g in
          uu____1371.FStar_TypeChecker_Env.guard_f in
        match uu____1370 with
        | FStar_TypeChecker_Common.Trivial  -> ret ()
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____1375 = istrivial e f in
            if uu____1375
            then ret ()
            else
              (let uu____1379 = mk_irrelevant_goal e f opts in
               bind uu____1379
                 (fun goal  ->
                    let goal1 =
                      let uu___93_1386 = goal in
                      {
                        context = (uu___93_1386.context);
                        witness = (uu___93_1386.witness);
                        goal_ty = (uu___93_1386.goal_ty);
                        opts = (uu___93_1386.opts);
                        is_guard = true
                      } in
                    push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1392 = is_irrelevant g in
       if uu____1392
       then bind dismiss (fun uu____1396  -> add_smt_goals [g])
       else
         (let uu____1398 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1398))
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
             let uu____1444 =
               try
                 let uu____1478 = FStar_List.splitAt n1 p.goals in
                 ret uu____1478
               with | uu____1508 -> fail "divide: not enough goals" in
             bind uu____1444
               (fun uu____1535  ->
                  match uu____1535 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___94_1561 = p in
                        {
                          main_context = (uu___94_1561.main_context);
                          main_goal = (uu___94_1561.main_goal);
                          all_implicits = (uu___94_1561.all_implicits);
                          goals = lgs;
                          smt_goals = []
                        } in
                      let rp =
                        let uu___95_1563 = p in
                        {
                          main_context = (uu___95_1563.main_context);
                          main_goal = (uu___95_1563.main_goal);
                          all_implicits = (uu___95_1563.all_implicits);
                          goals = rgs;
                          smt_goals = []
                        } in
                      let uu____1564 = set lp in
                      bind uu____1564
                        (fun uu____1572  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1586 = set rp in
                                     bind uu____1586
                                       (fun uu____1594  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___96_1610 = p in
                                                      {
                                                        main_context =
                                                          (uu___96_1610.main_context);
                                                        main_goal =
                                                          (uu___96_1610.main_goal);
                                                        all_implicits =
                                                          (uu___96_1610.all_implicits);
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
                                                    let uu____1611 = set p' in
                                                    bind uu____1611
                                                      (fun uu____1619  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1639 = divide (Prims.parse_int "1") f idtac in
    bind uu____1639
      (fun uu____1652  -> match uu____1652 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.goals with
         | [] -> ret []
         | uu____1687::uu____1688 ->
             let uu____1691 =
               let uu____1700 = map tau in
               divide (Prims.parse_int "1") tau uu____1700 in
             bind uu____1691
               (fun uu____1718  ->
                  match uu____1718 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1757 =
        bind t1
          (fun uu____1762  ->
             let uu____1763 = map t2 in
             bind uu____1763 (fun uu____1771  -> ret ())) in
      focus uu____1757
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1782 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1782 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1797 =
             let uu____1798 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1798 in
           if uu____1797
           then fail "Codomain is effectful"
           else
             (let env' = FStar_TypeChecker_Env.push_binders goal.context [b] in
              let typ' = comp_to_typ c in
              let uu____1804 = new_uvar env' typ' in
              bind uu____1804
                (fun u  ->
                   let uu____1811 =
                     let uu____1812 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     FStar_TypeChecker_Rel.teq_nosmt goal.context
                       goal.witness uu____1812 in
                   if uu____1811
                   then
                     let uu____1815 =
                       let uu____1818 =
                         let uu___99_1819 = goal in
                         let uu____1820 = bnorm env' u in
                         let uu____1821 = bnorm env' typ' in
                         {
                           context = env';
                           witness = uu____1820;
                           goal_ty = uu____1821;
                           opts = (uu___99_1819.opts);
                           is_guard = (uu___99_1819.is_guard)
                         } in
                       replace_cur uu____1818 in
                     bind uu____1815 (fun uu____1823  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1829 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1829)
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
       (let uu____1850 = FStar_Syntax_Util.arrow_one goal.goal_ty in
        match uu____1850 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1869 =
              let uu____1870 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1870 in
            if uu____1869
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None goal.goal_ty in
               let bs =
                 let uu____1886 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1886; b] in
               let env' = FStar_TypeChecker_Env.push_binders goal.context bs in
               let uu____1888 =
                 let uu____1891 = comp_to_typ c in new_uvar env' uu____1891 in
               bind uu____1888
                 (fun u  ->
                    let lb =
                      let uu____1908 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.goal_ty FStar_Parser_Const.effect_Tot_lid
                        uu____1908 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1912 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1912 with
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
                            let uu____1950 =
                              let uu____1953 =
                                let uu___100_1954 = goal in
                                let uu____1955 = bnorm env' u in
                                let uu____1956 =
                                  let uu____1957 = comp_to_typ c in
                                  bnorm env' uu____1957 in
                                {
                                  context = env';
                                  witness = uu____1955;
                                  goal_ty = uu____1956;
                                  opts = (uu___100_1954.opts);
                                  is_guard = (uu___100_1954.is_guard)
                                } in
                              replace_cur uu____1953 in
                            bind uu____1950
                              (fun uu____1964  ->
                                 let uu____1965 =
                                   let uu____1970 =
                                     FStar_Syntax_Syntax.mk_binder bv in
                                   (uu____1970, b) in
                                 ret uu____1965)
                          else fail "intro_rec: unification failed"))))
        | FStar_Pervasives_Native.None  ->
            let uu____1984 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1984))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2009 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2009 in
         let w = normalize steps goal.context goal.witness in
         let t = normalize steps goal.context goal.goal_ty in
         replace_cur
           (let uu___101_2016 = goal in
            {
              context = (uu___101_2016.context);
              witness = w;
              goal_ty = t;
              opts = (uu___101_2016.opts);
              is_guard = (uu___101_2016.is_guard)
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
             let uu____2040 = FStar_TypeChecker_Normalize.tr_norm_steps s in
             FStar_List.append
               [FStar_TypeChecker_Normalize.Reify;
               FStar_TypeChecker_Normalize.UnfoldTac] uu____2040 in
           let t1 = normalize steps ps.main_context t in ret t1)
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2055 =
           try
             let uu____2083 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____2083
           with
           | e ->
               let uu____2110 = FStar_Syntax_Print.term_to_string t in
               let uu____2111 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____2110
                 uu____2111 in
         bind uu____2055
           (fun uu____2129  ->
              match uu____2129 with
              | (t1,typ,guard) ->
                  let uu____2141 =
                    let uu____2142 =
                      let uu____2143 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2143 in
                    Prims.op_Negation uu____2142 in
                  if uu____2141
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2147 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____2147
                     then (solve goal t1; dismiss)
                     else
                       (let uu____2152 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____2153 =
                          let uu____2154 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____2154 in
                        let uu____2155 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2152 uu____2153 uu____2155))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  -> let uu____2164 = __exact t in focus uu____2164
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2178 =
           try
             let uu____2206 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____2206
           with
           | e ->
               let uu____2233 = FStar_Syntax_Print.term_to_string t in
               let uu____2234 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2233
                 uu____2234 in
         bind uu____2178
           (fun uu____2252  ->
              match uu____2252 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2270 =
                       let uu____2271 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2271 in
                     if uu____2270
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2275 =
                          let uu____2284 =
                            let uu____2293 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2293.FStar_Syntax_Syntax.effect_args in
                          match uu____2284 with
                          | pre::post::uu____2304 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2345 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2275 with
                        | (pre,post) ->
                            let uu____2374 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____2374
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____2379  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____2381 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____2382 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____2383 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2381 uu____2382 uu____2383)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.is_guard
      then false
      else
        (let free_uvars =
           let uu____2396 =
             let uu____2403 = FStar_Syntax_Free.uvars g.goal_ty in
             FStar_Util.set_elements uu____2403 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2396 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2430 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2450 =
               let uu____2455 = __exact tm in trytac uu____2455 in
             bind uu____2450
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2468 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2468 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           let uu____2498 =
                             let uu____2499 =
                               FStar_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu____2499 in
                           if uu____2498
                           then fail "apply: not total codomain"
                           else
                             (let uu____2503 =
                                new_uvar goal.context
                                  bv.FStar_Syntax_Syntax.sort in
                              bind uu____2503
                                (fun u  ->
                                   let tm' =
                                     FStar_Syntax_Syntax.mk_Tm_app tm
                                       [(u, aq)] FStar_Pervasives_Native.None
                                       (goal.context).FStar_TypeChecker_Env.range in
                                   let typ' =
                                     let uu____2523 = comp_to_typ c in
                                     FStar_All.pipe_left
                                       (FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.NT (bv, u)])
                                       uu____2523 in
                                   let uu____2524 = __apply uopt tm' typ' in
                                   bind uu____2524
                                     (fun uu____2531  ->
                                        let uu____2532 =
                                          let uu____2533 =
                                            let uu____2536 =
                                              let uu____2537 =
                                                FStar_Syntax_Util.head_and_args
                                                  u in
                                              FStar_Pervasives_Native.fst
                                                uu____2537 in
                                            FStar_Syntax_Subst.compress
                                              uu____2536 in
                                          uu____2533.FStar_Syntax_Syntax.n in
                                        match uu____2532 with
                                        | FStar_Syntax_Syntax.Tm_uvar
                                            (uvar,uu____2565) ->
                                            bind get
                                              (fun ps  ->
                                                 let uu____2593 =
                                                   uopt &&
                                                     (uvar_free uvar ps) in
                                                 if uu____2593
                                                 then ret ()
                                                 else
                                                   (let uu____2597 =
                                                      let uu____2600 =
                                                        let uu___106_2601 =
                                                          goal in
                                                        let uu____2602 =
                                                          bnorm goal.context
                                                            u in
                                                        let uu____2603 =
                                                          bnorm goal.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          context =
                                                            (uu___106_2601.context);
                                                          witness =
                                                            uu____2602;
                                                          goal_ty =
                                                            uu____2603;
                                                          opts =
                                                            (uu___106_2601.opts);
                                                          is_guard = false
                                                        } in
                                                      [uu____2600] in
                                                    add_goals uu____2597))
                                        | uu____2604 -> ret ()))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2662 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____2662 with
           | (tm1,typ,guard) ->
               let uu____2674 =
                 let uu____2677 =
                   let uu____2680 = __apply uopt tm1 typ in
                   bind uu____2680
                     (fun uu____2684  ->
                        add_goal_from_guard goal.context guard goal.opts) in
                 focus uu____2677 in
               let uu____2685 =
                 let uu____2688 = FStar_Syntax_Print.term_to_string tm1 in
                 let uu____2689 = FStar_Syntax_Print.term_to_string typ in
                 let uu____2690 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 fail3
                   "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                   uu____2688 uu____2689 uu____2690 in
               try_unif uu____2674 uu____2685)
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2699 =
      let is_unit_t t =
        let uu____2706 =
          let uu____2707 = FStar_Syntax_Subst.compress t in
          uu____2707.FStar_Syntax_Syntax.n in
        match uu____2706 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
            true
        | uu____2711 -> false in
      bind cur_goal
        (fun goal  ->
           let uu____2721 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____2721 with
           | (tm1,t,guard) ->
               let uu____2733 = FStar_Syntax_Util.arrow_formals_comp t in
               (match uu____2733 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2763 =
                         FStar_List.fold_left
                           (fun uu____2809  ->
                              fun uu____2810  ->
                                match (uu____2809, uu____2810) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2913 = is_unit_t b_t in
                                    if uu____2913
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____2951 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.context b_t in
                                       match uu____2951 with
                                       | (u,uu____2981,g_u) ->
                                           let uu____2995 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____2995,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2763 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____3065 =
                             let uu____3074 =
                               let uu____3083 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____3083.FStar_Syntax_Syntax.effect_args in
                             match uu____3074 with
                             | pre::post::uu____3094 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____3135 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____3065 with
                            | (pre,post) ->
                                let uu____3164 =
                                  let uu____3167 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____3167 goal.goal_ty in
                                (match uu____3164 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____3170 =
                                       let uu____3171 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____3171 in
                                     let uu____3172 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____3170 uu____3172
                                 | FStar_Pervasives_Native.Some g ->
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____3244  ->
                                               match uu____3244 with
                                               | (uu____3257,uu____3258,uu____3259,tm2,uu____3261,uu____3262)
                                                   ->
                                                   let uu____3263 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____3263 with
                                                    | (hd1,uu____3279) ->
                                                        let uu____3300 =
                                                          let uu____3301 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____3301.FStar_Syntax_Syntax.n in
                                                        (match uu____3300
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____3304 ->
                                                             true
                                                         | uu____3321 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let uu____3323 =
                                         add_implicits implicits1 in
                                       bind uu____3323
                                         (fun uu____3327  ->
                                            bind dismiss
                                              (fun uu____3336  ->
                                                 let is_free_uvar uv t1 =
                                                   let free_uvars =
                                                     let uu____3347 =
                                                       let uu____3354 =
                                                         FStar_Syntax_Free.uvars
                                                           t1 in
                                                       FStar_Util.set_elements
                                                         uu____3354 in
                                                     FStar_List.map
                                                       FStar_Pervasives_Native.fst
                                                       uu____3347 in
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
                                                   let uu____3395 =
                                                     FStar_Syntax_Util.head_and_args
                                                       t1 in
                                                   match uu____3395 with
                                                   | (hd1,uu____3411) ->
                                                       (match hd1.FStar_Syntax_Syntax.n
                                                        with
                                                        | FStar_Syntax_Syntax.Tm_uvar
                                                            (uv,uu____3433)
                                                            ->
                                                            appears uv goals
                                                        | uu____3458 -> false) in
                                                 let sub_goals =
                                                   FStar_All.pipe_right
                                                     implicits1
                                                     (FStar_List.map
                                                        (fun uu____3500  ->
                                                           match uu____3500
                                                           with
                                                           | (_msg,_env,_uvar,term,typ,uu____3518)
                                                               ->
                                                               let uu___109_3519
                                                                 = goal in
                                                               let uu____3520
                                                                 =
                                                                 bnorm
                                                                   goal.context
                                                                   term in
                                                               let uu____3521
                                                                 =
                                                                 bnorm
                                                                   goal.context
                                                                   typ in
                                                               {
                                                                 context =
                                                                   (uu___109_3519.context);
                                                                 witness =
                                                                   uu____3520;
                                                                 goal_ty =
                                                                   uu____3521;
                                                                 opts =
                                                                   (uu___109_3519.opts);
                                                                 is_guard =
                                                                   (uu___109_3519.is_guard)
                                                               })) in
                                                 let rec filter' f xs =
                                                   match xs with
                                                   | [] -> []
                                                   | x::xs1 ->
                                                       let uu____3559 =
                                                         f x xs1 in
                                                       if uu____3559
                                                       then
                                                         let uu____3562 =
                                                           filter' f xs1 in
                                                         x :: uu____3562
                                                       else filter' f xs1 in
                                                 let sub_goals1 =
                                                   filter'
                                                     (fun g1  ->
                                                        fun goals  ->
                                                          let uu____3576 =
                                                            checkone
                                                              g1.witness
                                                              goals in
                                                          Prims.op_Negation
                                                            uu____3576)
                                                     sub_goals in
                                                 let uu____3577 =
                                                   add_goal_from_guard
                                                     goal.context guard
                                                     goal.opts in
                                                 bind uu____3577
                                                   (fun uu____3582  ->
                                                      let uu____3583 =
                                                        add_goal_from_guard
                                                          goal.context g
                                                          goal.opts in
                                                      bind uu____3583
                                                        (fun uu____3588  ->
                                                           let uu____3589 =
                                                             add_irrelevant_goal
                                                               goal.context
                                                               pre goal.opts in
                                                           bind uu____3589
                                                             (fun uu____3594 
                                                                ->
                                                                let uu____3595
                                                                  =
                                                                  trytac
                                                                    trivial in
                                                                bind
                                                                  uu____3595
                                                                  (fun
                                                                    uu____3603
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))) in
    focus uu____2699
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3622 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3622 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3632::(e1,uu____3634)::(e2,uu____3636)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3695 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3718 = destruct_eq' typ in
    match uu____3718 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3748 = FStar_Syntax_Util.un_squash typ in
        (match uu____3748 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3781 =
           FStar_All.pipe_left mlog
             (fun uu____3791  ->
                let uu____3792 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3793 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3792
                  uu____3793) in
         bind uu____3781
           (fun uu____3801  ->
              let uu____3802 =
                let uu____3809 =
                  let uu____3810 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3810 in
                destruct_eq uu____3809 in
              match uu____3802 with
              | FStar_Pervasives_Native.Some (x,e) ->
                  let uu____3827 =
                    let uu____3828 = FStar_Syntax_Subst.compress x in
                    uu____3828.FStar_Syntax_Syntax.n in
                  (match uu____3827 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___110_3835 = goal in
                         let uu____3836 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____3837 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___110_3835.context);
                           witness = uu____3836;
                           goal_ty = uu____3837;
                           opts = (uu___110_3835.opts);
                           is_guard = (uu___110_3835.is_guard)
                         } in
                       replace_cur goal1
                   | uu____3838 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3839 -> fail "Not an equality hypothesis"))
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
            let uu____3870 = FStar_TypeChecker_Env.pop_bv e in
            match uu____3870 with
            | FStar_Pervasives_Native.None  -> e
            | FStar_Pervasives_Native.Some (bv,e') ->
                if FStar_Syntax_Syntax.bv_eq bv b1
                then FStar_TypeChecker_Env.push_bv e' b2
                else
                  (let uu____3888 = alpha e' in
                   let uu____3889 =
                     let uu___111_3890 = bv in
                     let uu____3891 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___111_3890.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___111_3890.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3891
                     } in
                   FStar_TypeChecker_Env.push_bv uu____3888 uu____3889) in
          let c = alpha g.context in
          let w = FStar_Syntax_Subst.subst s g.witness in
          let t = FStar_Syntax_Subst.subst s g.goal_ty in
          let uu___112_3897 = g in
          {
            context = c;
            witness = w;
            goal_ty = t;
            opts = (uu___112_3897.opts);
            is_guard = (uu___112_3897.is_guard)
          }
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3918 = b in
           match uu____3918 with
           | (bv,uu____3922) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___113_3926 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___113_3926.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___113_3926.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3930 =
                   let uu____3931 =
                     let uu____3938 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3938) in
                   FStar_Syntax_Syntax.NT uu____3931 in
                 [uu____3930] in
               let uu____3939 = subst_goal bv bv' s1 goal in
               replace_cur uu____3939)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3945 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____3945 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____3967 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____3967 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___114_4001 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___114_4001.opts);
                is_guard = (uu___114_4001.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4013 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____4013 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4034 = FStar_Syntax_Print.bv_to_string x in
               let uu____4035 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4034 uu____4035
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4042 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____4042 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let uu____4064 = FStar_Util.set_mem x fns_ty in
           if uu____4064
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4068 = new_uvar env' goal.goal_ty in
              bind uu____4068
                (fun u  ->
                   let uu____4074 =
                     let uu____4075 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context
                         goal.witness u in
                     Prims.op_Negation uu____4075 in
                   if uu____4074
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___115_4080 = goal in
                        let uu____4081 = bnorm env' u in
                        {
                          context = env';
                          witness = uu____4081;
                          goal_ty = (uu___115_4080.goal_ty);
                          opts = (uu___115_4080.opts);
                          is_guard = (uu___115_4080.is_guard)
                        } in
                      bind dismiss (fun uu____4083  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4095 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____4095 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4119  ->
                    let uu____4120 = clear b in
                    bind uu____4120
                      (fun uu____4124  ->
                         bind intro (fun uu____4126  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___116_4143 = g in
           {
             context = ctx';
             witness = (uu___116_4143.witness);
             goal_ty = (uu___116_4143.goal_ty);
             opts = (uu___116_4143.opts);
             is_guard = (uu___116_4143.is_guard)
           } in
         bind dismiss (fun uu____4145  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___117_4162 = g in
           {
             context = ctx';
             witness = (uu___117_4162.witness);
             goal_ty = (uu___117_4162.goal_ty);
             opts = (uu___117_4162.opts);
             is_guard = (uu___117_4162.is_guard)
           } in
         bind dismiss (fun uu____4164  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4206 = f x in
          bind uu____4206
            (fun y  ->
               let uu____4214 = mapM f xs in
               bind uu____4214 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4260 = FStar_Syntax_Subst.compress t in
          uu____4260.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4295 = ff hd1 in
              bind uu____4295
                (fun hd2  ->
                   let fa uu____4315 =
                     match uu____4315 with
                     | (a,q) ->
                         let uu____4328 = ff a in
                         bind uu____4328 (fun a1  -> ret (a1, q)) in
                   let uu____4341 = mapM fa args in
                   bind uu____4341
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4401 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4401 with
               | (bs1,t') ->
                   let uu____4410 =
                     let uu____4413 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4413 t' in
                   bind uu____4410
                     (fun t''  ->
                        let uu____4417 =
                          let uu____4418 =
                            let uu____4435 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4436 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4435, uu____4436, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4418 in
                        ret uu____4417))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4457 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___118_4461 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___118_4461.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___118_4461.FStar_Syntax_Syntax.vars)
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
            let uu____4490 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4490 with
            | (t1,lcomp,g) ->
                let uu____4502 =
                  let uu____4503 = FStar_TypeChecker_Rel.is_trivial g in
                  Prims.op_Negation uu____4503 in
                if uu____4502
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4510 = new_uvar env typ in
                   bind uu____4510
                     (fun ut  ->
                        log ps
                          (fun uu____4521  ->
                             let uu____4522 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4523 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4522 uu____4523);
                        (let uu____4524 =
                           let uu____4527 =
                             let uu____4528 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4528 typ t1 ut in
                           add_irrelevant_goal env uu____4527 opts in
                         bind uu____4524
                           (fun uu____4531  ->
                              let uu____4532 =
                                bind tau
                                  (fun uu____4537  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4532))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4558 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4558 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____4595  ->
                   let uu____4596 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4596);
              bind dismiss_all
                (fun uu____4599  ->
                   let uu____4600 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____4600
                     (fun gt'  ->
                        log ps
                          (fun uu____4610  ->
                             let uu____4611 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4611);
                        (let uu____4612 = push_goals gs in
                         bind uu____4612
                           (fun uu____4616  ->
                              add_goals
                                [(let uu___119_4618 = g in
                                  {
                                    context = (uu___119_4618.context);
                                    witness = (uu___119_4618.witness);
                                    goal_ty = gt';
                                    opts = (uu___119_4618.opts);
                                    is_guard = (uu___119_4618.is_guard)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4638 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____4638 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4650 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4650 with
            | (hd1,args) ->
                let uu____4683 =
                  let uu____4696 =
                    let uu____4697 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4697.FStar_Syntax_Syntax.n in
                  (uu____4696, args) in
                (match uu____4683 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4711::(l,uu____4713)::(r,uu____4715)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4762 =
                       let uu____4763 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____4763 in
                     if uu____4762
                     then
                       let uu____4766 = FStar_Syntax_Print.term_to_string l in
                       let uu____4767 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4766 uu____4767
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____4771) ->
                     let uu____4788 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____4788))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4796 = new_uvar g.context g.goal_ty in
       bind uu____4796
         (fun u  ->
            let g' =
              let uu___120_4803 = g in
              {
                context = (uu___120_4803.context);
                witness = u;
                goal_ty = (uu___120_4803.goal_ty);
                opts = (uu___120_4803.opts);
                is_guard = (uu___120_4803.is_guard)
              } in
            bind dismiss
              (fun uu____4806  ->
                 let uu____4807 =
                   let uu____4810 =
                     let uu____4811 =
                       FStar_TypeChecker_TcTerm.universe_of g.context
                         g.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4811 g.goal_ty u
                       g.witness in
                   add_irrelevant_goal g.context uu____4810 g.opts in
                 bind uu____4807
                   (fun uu____4814  ->
                      let uu____4815 = add_goals [g'] in
                      bind uu____4815 (fun uu____4819  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___121_4836 = ps in
              {
                main_context = (uu___121_4836.main_context);
                main_goal = (uu___121_4836.main_goal);
                all_implicits = (uu___121_4836.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___121_4836.smt_goals)
              })
       | uu____4837 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___122_4852 = ps in
              {
                main_context = (uu___122_4852.main_context);
                main_goal = (uu___122_4852.main_goal);
                all_implicits = (uu___122_4852.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___122_4852.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____4859 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____4901 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____4901 with
         | (t1,typ,guard) ->
             let uu____4917 = FStar_Syntax_Util.head_and_args typ in
             (match uu____4917 with
              | (hd1,args) ->
                  let uu____4960 =
                    let uu____4973 =
                      let uu____4974 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____4974.FStar_Syntax_Syntax.n in
                    (uu____4973, args) in
                  (match uu____4960 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____4993)::(q,uu____4995)::[]) when
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
                         let uu___123_5033 = g in
                         let uu____5034 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____5034;
                           witness = (uu___123_5033.witness);
                           goal_ty = (uu___123_5033.goal_ty);
                           opts = (uu___123_5033.opts);
                           is_guard = (uu___123_5033.is_guard)
                         } in
                       let g2 =
                         let uu___124_5036 = g in
                         let uu____5037 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____5037;
                           witness = (uu___124_5036.witness);
                           goal_ty = (uu___124_5036.goal_ty);
                           opts = (uu___124_5036.opts);
                           is_guard = (uu___124_5036.is_guard)
                         } in
                       bind dismiss
                         (fun uu____5044  ->
                            let uu____5045 = add_goals [g1; g2] in
                            bind uu____5045
                              (fun uu____5054  ->
                                 let uu____5055 =
                                   let uu____5060 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____5061 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____5060, uu____5061) in
                                 ret uu____5055))
                   | uu____5066 ->
                       let uu____5079 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____5079)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5102 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____5102);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___125_5109 = g in
                 {
                   context = (uu___125_5109.context);
                   witness = (uu___125_5109.witness);
                   goal_ty = (uu___125_5109.goal_ty);
                   opts = opts';
                   is_guard = (uu___125_5109.is_guard)
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
           let uu____5150 =
             (goal.context).FStar_TypeChecker_Env.type_of env tm in
           match uu____5150 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5179 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5185 =
              let uu____5186 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5186 in
            new_uvar env uu____5185 in
      bind uu____5179
        (fun typ  ->
           let uu____5198 = new_uvar env typ in
           bind uu____5198 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5218 =
             FStar_TypeChecker_Rel.teq_nosmt ps.main_context t1 t2 in
           ret uu____5218)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5238  ->
             let uu____5239 = FStar_Options.unsafe_tactic_exec () in
             if uu____5239
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5245  -> fun uu____5246  -> false) in
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
      let uu____5268 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5268 with
      | (u,uu____5286,g_u) ->
          let g =
            let uu____5301 = FStar_Options.peek () in
            {
              context = env;
              witness = u;
              goal_ty = typ;
              opts = uu____5301;
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
      let uu____5318 = goal_of_goal_ty env typ in
      match uu____5318 with
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