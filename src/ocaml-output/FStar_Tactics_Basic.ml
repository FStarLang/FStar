open Prims
type name = FStar_Syntax_Syntax.bv[@@deriving show]
type env = FStar_TypeChecker_Env.env[@@deriving show]
type implicits = FStar_TypeChecker_Env.implicits[@@deriving show]
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
exception TacFailure of Prims.string
let uu___is_TacFailure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | TacFailure uu____32 -> true | uu____33 -> false
let __proj__TacFailure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | TacFailure uu____41 -> uu____41
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result;}
[@@deriving show]
let __proj__Mktac__item__tac_f:
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun projectee  ->
    match projectee with | { tac_f = __fname__tac_f;_} -> __fname__tac_f
let mk_tac:
  'a .
    (FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result) ->
      'a tac
  = fun f  -> { tac_f = f }
let run:
  'Auu____105 .
    'Auu____105 tac ->
      FStar_Tactics_Types.proofstate ->
        'Auu____105 FStar_Tactics_Result.__result
  = fun t  -> fun p  -> t.tac_f p
let ret: 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p))
let bind: 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____172 = run t1 p in
           match uu____172 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____179 = t2 a in run uu____179 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: FStar_Tactics_Types.goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____191 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____191
        (FStar_Syntax_Print.binders_to_string ", ") in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
    let uu____194 = FStar_Syntax_Print.term_to_string w in
    let uu____195 = FStar_Syntax_Print.term_to_string t in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____194 uu____195
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____208 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____208
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____221 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____221
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____238 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____238
let comp_to_typ: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____244) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____254) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: FStar_Tactics_Types.goal -> Prims.bool =
  fun g  ->
    let uu____268 =
      let uu____273 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty in
      FStar_Syntax_Util.un_squash uu____273 in
    match uu____268 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____279 -> false
let dump_goal:
  'Auu____290 . 'Auu____290 -> FStar_Tactics_Types.goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____300 = goal_to_string goal in tacprint uu____300
let dump_cur: FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____310 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____314 = FStar_List.hd ps.FStar_Tactics_Types.goals in
            dump_goal ps uu____314))
let ps_to_string:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu____322  ->
    match uu____322 with
    | (msg,ps) ->
        let uu____329 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.goals) in
        let uu____330 =
          let uu____331 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.goals in
          FStar_String.concat "\n" uu____331 in
        let uu____334 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.smt_goals) in
        let uu____335 =
          let uu____336 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.smt_goals in
          FStar_String.concat "\n" uu____336 in
        FStar_Util.format5
          "State dump (%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s" msg
          uu____329 uu____330 uu____334 uu____335
let goal_to_json: FStar_Tactics_Types.goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____344 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____344 FStar_Syntax_Print.binders_to_json in
    let uu____345 =
      let uu____352 =
        let uu____359 =
          let uu____364 =
            let uu____365 =
              let uu____372 =
                let uu____377 =
                  let uu____378 =
                    FStar_Syntax_Print.term_to_string
                      g.FStar_Tactics_Types.witness in
                  FStar_Util.JsonStr uu____378 in
                ("witness", uu____377) in
              let uu____379 =
                let uu____386 =
                  let uu____391 =
                    let uu____392 =
                      FStar_Syntax_Print.term_to_string
                        g.FStar_Tactics_Types.goal_ty in
                    FStar_Util.JsonStr uu____392 in
                  ("type", uu____391) in
                [uu____386] in
              uu____372 :: uu____379 in
            FStar_Util.JsonAssoc uu____365 in
          ("goal", uu____364) in
        [uu____359] in
      ("hyps", g_binders) :: uu____352 in
    FStar_Util.JsonAssoc uu____345
let ps_to_json:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____424  ->
    match uu____424 with
    | (msg,ps) ->
        let uu____431 =
          let uu____438 =
            let uu____445 =
              let uu____450 =
                let uu____451 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals in
                FStar_Util.JsonList uu____451 in
              ("goals", uu____450) in
            let uu____454 =
              let uu____461 =
                let uu____466 =
                  let uu____467 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals in
                  FStar_Util.JsonList uu____467 in
                ("smt-goals", uu____466) in
              [uu____461] in
            uu____445 :: uu____454 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____438 in
        FStar_Util.JsonAssoc uu____431
let dump_proofstate:
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____496  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
let print_proof_state1: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac (fun p  -> dump_cur p msg; FStar_Tactics_Result.Success ((), p))
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac
      (fun p  -> dump_proofstate p msg; FStar_Tactics_Result.Success ((), p))
let get: FStar_Tactics_Types.proofstate tac =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p))
let tac_verb_dbg: Prims.bool FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let rec log:
  FStar_Tactics_Types.proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit
  =
  fun ps  ->
    fun f  ->
      let uu____556 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____556 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____578 =
              let uu____581 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____581 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____578);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail: 'Auu____621 . Prims.string -> 'Auu____621 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____632 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____632
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____640 . Prims.string -> Prims.string -> 'Auu____640 tac =
  fun msg  ->
    fun x  -> let uu____651 = FStar_Util.format1 msg x in fail uu____651
let fail2:
  'Auu____660 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____660 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____675 = FStar_Util.format2 msg x y in fail uu____675
let fail3:
  'Auu____686 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____686 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____705 = FStar_Util.format3 msg x y z in fail uu____705
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____733 = run t ps in
         match uu____733 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success
                ((FStar_Pervasives_Native.Some a), q))
         | FStar_Tactics_Result.Failed (uu____747,uu____748) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____763  -> FStar_Tactics_Result.Success ((), p))
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun goal  ->
    fun solution  ->
      FStar_TypeChecker_Rel.teq_nosmt goal.FStar_Tactics_Types.context
        goal.FStar_Tactics_Types.witness solution
let solve: FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun goal  ->
    fun solution  ->
      let uu____780 = trysolve goal solution in
      if uu____780
      then ()
      else
        (let uu____782 =
           let uu____783 =
             let uu____784 =
               FStar_TypeChecker_Normalize.term_to_string
                 goal.FStar_Tactics_Types.context solution in
             let uu____785 =
               FStar_TypeChecker_Normalize.term_to_string
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.witness in
             let uu____786 =
               FStar_Syntax_Print.term_to_string
                 goal.FStar_Tactics_Types.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____784
               uu____785 uu____786 in
           TacFailure uu____783 in
         FStar_Exn.raise uu____782)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____792 =
         let uu___88_793 = p in
         let uu____794 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___88_793.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___88_793.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___88_793.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____794;
           FStar_Tactics_Types.smt_goals =
             (uu___88_793.FStar_Tactics_Types.smt_goals)
         } in
       set uu____792)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___89_803 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___89_803.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___89_803.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___89_803.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___89_803.FStar_Tactics_Types.smt_goals)
          }))
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___90_820 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___90_820.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___90_820.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___90_820.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___90_820.FStar_Tactics_Types.smt_goals)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___91_837 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___91_837.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___91_837.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___91_837.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___91_837.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___92_854 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___92_854.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___92_854.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___92_854.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___92_854.FStar_Tactics_Types.smt_goals)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___93_871 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___93_871.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___93_871.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___93_871.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___93_871.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____881  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___94_894 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___94_894.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___94_894.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___94_894.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___94_894.FStar_Tactics_Types.smt_goals)
            }))
let new_uvar: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun typ  ->
      let uu____919 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____919 with
      | (u,uu____935,g_u) ->
          let uu____949 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____949 (fun uu____953  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____958 = FStar_Syntax_Util.un_squash t in
    match uu____958 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____968 =
          let uu____969 = FStar_Syntax_Subst.compress t' in
          uu____969.FStar_Syntax_Syntax.n in
        (match uu____968 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____973 -> false)
    | uu____974 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____983 = FStar_Syntax_Util.un_squash t in
    match uu____983 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____993 =
          let uu____994 = FStar_Syntax_Subst.compress t' in
          uu____994.FStar_Syntax_Syntax.n in
        (match uu____993 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____998 -> false)
    | uu____999 -> false
let cur_goal: FStar_Tactics_Types.goal tac =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let mk_irrelevant_goal:
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Options.optionstate -> FStar_Tactics_Types.goal tac
  =
  fun env  ->
    fun phi  ->
      fun opts  ->
        let typ = FStar_Syntax_Util.mk_squash phi in
        let uu____1033 = new_uvar env typ in
        bind uu____1033
          (fun u  ->
             let goal =
               {
                 FStar_Tactics_Types.context = env;
                 FStar_Tactics_Types.witness = u;
                 FStar_Tactics_Types.goal_ty = typ;
                 FStar_Tactics_Types.opts = opts;
                 FStar_Tactics_Types.is_guard = false
               } in
             ret goal)
let add_irrelevant_goal:
  env ->
    FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun env  ->
    fun phi  ->
      fun opts  ->
        let uu____1056 = mk_irrelevant_goal env phi opts in
        bind uu____1056 (fun goal  -> add_goals [goal])
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
       let uu____1079 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1079
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____1084 =
            FStar_Syntax_Print.term_to_string
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1084))
let add_goal_from_guard:
  env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Options.optionstate -> Prims.unit tac
  =
  fun e  ->
    fun g  ->
      fun opts  ->
        let uu____1101 =
          let uu____1102 = FStar_TypeChecker_Rel.simplify_guard e g in
          uu____1102.FStar_TypeChecker_Env.guard_f in
        match uu____1101 with
        | FStar_TypeChecker_Common.Trivial  -> ret ()
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____1106 = istrivial e f in
            if uu____1106
            then ret ()
            else
              (let uu____1110 = mk_irrelevant_goal e f opts in
               bind uu____1110
                 (fun goal  ->
                    let goal1 =
                      let uu___95_1117 = goal in
                      {
                        FStar_Tactics_Types.context =
                          (uu___95_1117.FStar_Tactics_Types.context);
                        FStar_Tactics_Types.witness =
                          (uu___95_1117.FStar_Tactics_Types.witness);
                        FStar_Tactics_Types.goal_ty =
                          (uu___95_1117.FStar_Tactics_Types.goal_ty);
                        FStar_Tactics_Types.opts =
                          (uu___95_1117.FStar_Tactics_Types.opts);
                        FStar_Tactics_Types.is_guard = true
                      } in
                    push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1123 = is_irrelevant g in
       if uu____1123
       then bind dismiss (fun uu____1127  -> add_smt_goals [g])
       else
         (let uu____1129 =
            FStar_Syntax_Print.term_to_string g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1129))
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
             let uu____1175 =
               try
                 let uu____1209 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1209
               with | uu____1239 -> fail "divide: not enough goals" in
             bind uu____1175
               (fun uu____1266  ->
                  match uu____1266 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___96_1292 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___96_1292.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___96_1292.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___96_1292.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = []
                        } in
                      let rp =
                        let uu___97_1294 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___97_1294.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___97_1294.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___97_1294.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = []
                        } in
                      let uu____1295 = set lp in
                      bind uu____1295
                        (fun uu____1303  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1317 = set rp in
                                     bind uu____1317
                                       (fun uu____1325  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___98_1341 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___98_1341.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___98_1341.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___98_1341.FStar_Tactics_Types.all_implicits);
                                                        FStar_Tactics_Types.goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.goals
                                                             rp'.FStar_Tactics_Types.goals);
                                                        FStar_Tactics_Types.smt_goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.smt_goals
                                                             (FStar_List.append
                                                                rp'.FStar_Tactics_Types.smt_goals
                                                                p.FStar_Tactics_Types.smt_goals))
                                                      } in
                                                    let uu____1342 = set p' in
                                                    bind uu____1342
                                                      (fun uu____1350  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1370 = divide (Prims.parse_int "1") f idtac in
    bind uu____1370
      (fun uu____1383  -> match uu____1383 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1418::uu____1419 ->
             let uu____1422 =
               let uu____1431 = map tau in
               divide (Prims.parse_int "1") tau uu____1431 in
             bind uu____1422
               (fun uu____1449  ->
                  match uu____1449 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1488 =
        bind t1
          (fun uu____1493  ->
             let uu____1494 = map t2 in
             bind uu____1494 (fun uu____1502  -> ret ())) in
      focus uu____1488
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1513 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1513 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1528 =
             let uu____1529 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1529 in
           if uu____1528
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1535 = new_uvar env' typ' in
              bind uu____1535
                (fun u  ->
                   let uu____1542 =
                     let uu____1543 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1543 in
                   if uu____1542
                   then
                     let uu____1546 =
                       let uu____1549 =
                         let uu___101_1550 = goal in
                         let uu____1551 = bnorm env' u in
                         let uu____1552 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1551;
                           FStar_Tactics_Types.goal_ty = uu____1552;
                           FStar_Tactics_Types.opts =
                             (uu___101_1550.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___101_1550.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1549 in
                     bind uu____1546 (fun uu____1554  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1560 =
             FStar_Syntax_Print.term_to_string
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1560)
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
       (let uu____1581 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1581 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1600 =
              let uu____1601 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1601 in
            if uu____1600
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1617 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1617; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1619 =
                 let uu____1622 = comp_to_typ c in new_uvar env' uu____1622 in
               bind uu____1619
                 (fun u  ->
                    let lb =
                      let uu____1639 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____1639 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1643 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1643 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        (FStar_Util.print_string "calling teq_nosmt\n";
                         (let res = trysolve goal tm in
                          if res
                          then
                            let uu____1681 =
                              let uu____1684 =
                                let uu___102_1685 = goal in
                                let uu____1686 = bnorm env' u in
                                let uu____1687 =
                                  let uu____1688 = comp_to_typ c in
                                  bnorm env' uu____1688 in
                                {
                                  FStar_Tactics_Types.context = env';
                                  FStar_Tactics_Types.witness = uu____1686;
                                  FStar_Tactics_Types.goal_ty = uu____1687;
                                  FStar_Tactics_Types.opts =
                                    (uu___102_1685.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___102_1685.FStar_Tactics_Types.is_guard)
                                } in
                              replace_cur uu____1684 in
                            bind uu____1681
                              (fun uu____1695  ->
                                 let uu____1696 =
                                   let uu____1701 =
                                     FStar_Syntax_Syntax.mk_binder bv in
                                   (uu____1701, b) in
                                 ret uu____1696)
                          else fail "intro_rec: unification failed"))))
        | FStar_Pervasives_Native.None  ->
            let uu____1715 =
              FStar_Syntax_Print.term_to_string
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1715))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____1740 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1740 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___103_1747 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___103_1747.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___103_1747.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___103_1747.FStar_Tactics_Types.is_guard)
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
             let uu____1771 = FStar_TypeChecker_Normalize.tr_norm_steps s in
             FStar_List.append
               [FStar_TypeChecker_Normalize.Reify;
               FStar_TypeChecker_Normalize.UnfoldTac] uu____1771 in
           let t1 = normalize steps ps.FStar_Tactics_Types.main_context t in
           ret t1)
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1786 =
           try
             let uu____1814 =
               (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
                 goal.FStar_Tactics_Types.context t in
             ret uu____1814
           with
           | e ->
               let uu____1841 = FStar_Syntax_Print.term_to_string t in
               let uu____1842 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1841
                 uu____1842 in
         bind uu____1786
           (fun uu____1860  ->
              match uu____1860 with
              | (t1,typ,guard) ->
                  let uu____1872 =
                    let uu____1873 =
                      let uu____1874 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1874 in
                    Prims.op_Negation uu____1873 in
                  if uu____1872
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1878 =
                       FStar_TypeChecker_Rel.teq_nosmt
                         goal.FStar_Tactics_Types.context typ
                         goal.FStar_Tactics_Types.goal_ty in
                     if uu____1878
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1883 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1884 =
                          let uu____1885 =
                            bnorm goal.FStar_Tactics_Types.context typ in
                          FStar_Syntax_Print.term_to_string uu____1885 in
                        let uu____1886 =
                          FStar_Syntax_Print.term_to_string
                            goal.FStar_Tactics_Types.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1883 uu____1884 uu____1886))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  -> let uu____1895 = __exact t in focus uu____1895
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1909 =
           try
             let uu____1937 =
               FStar_TypeChecker_TcTerm.tc_term
                 goal.FStar_Tactics_Types.context t in
             ret uu____1937
           with
           | e ->
               let uu____1964 = FStar_Syntax_Print.term_to_string t in
               let uu____1965 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1964
                 uu____1965 in
         bind uu____1909
           (fun uu____1983  ->
              match uu____1983 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2001 =
                       let uu____2002 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2002 in
                     if uu____2001
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2006 =
                          let uu____2015 =
                            let uu____2024 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2024.FStar_Syntax_Syntax.effect_args in
                          match uu____2015 with
                          | pre::post::uu____2035 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2076 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2006 with
                        | (pre,post) ->
                            let uu____2105 =
                              FStar_TypeChecker_Rel.teq_nosmt
                                goal.FStar_Tactics_Types.context post
                                goal.FStar_Tactics_Types.goal_ty in
                            if uu____2105
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____2110  ->
                                    add_irrelevant_goal
                                      goal.FStar_Tactics_Types.context pre
                                      goal.FStar_Tactics_Types.opts))
                            else
                              (let uu____2112 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____2113 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____2114 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.FStar_Tactics_Types.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2112 uu____2113 uu____2114)))))
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2127 =
             let uu____2134 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2134 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2127 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2161 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2181 =
               let uu____2186 = __exact tm in trytac uu____2186 in
             bind uu____2181
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2199 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2199 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           let uu____2229 =
                             let uu____2230 =
                               FStar_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu____2230 in
                           if uu____2229
                           then fail "apply: not total codomain"
                           else
                             (let uu____2234 =
                                new_uvar goal.FStar_Tactics_Types.context
                                  bv.FStar_Syntax_Syntax.sort in
                              bind uu____2234
                                (fun u  ->
                                   let tm' =
                                     FStar_Syntax_Syntax.mk_Tm_app tm
                                       [(u, aq)] FStar_Pervasives_Native.None
                                       (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                   let typ' =
                                     let uu____2254 = comp_to_typ c in
                                     FStar_All.pipe_left
                                       (FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.NT (bv, u)])
                                       uu____2254 in
                                   let uu____2255 = __apply uopt tm' typ' in
                                   bind uu____2255
                                     (fun uu____2262  ->
                                        let uu____2263 =
                                          let uu____2264 =
                                            let uu____2267 =
                                              let uu____2268 =
                                                FStar_Syntax_Util.head_and_args
                                                  u in
                                              FStar_Pervasives_Native.fst
                                                uu____2268 in
                                            FStar_Syntax_Subst.compress
                                              uu____2267 in
                                          uu____2264.FStar_Syntax_Syntax.n in
                                        match uu____2263 with
                                        | FStar_Syntax_Syntax.Tm_uvar
                                            (uvar,uu____2296) ->
                                            bind get
                                              (fun ps  ->
                                                 let uu____2324 =
                                                   uopt &&
                                                     (uvar_free uvar ps) in
                                                 if uu____2324
                                                 then ret ()
                                                 else
                                                   (let uu____2328 =
                                                      let uu____2331 =
                                                        let uu___108_2332 =
                                                          goal in
                                                        let uu____2333 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            u in
                                                        let uu____2334 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          FStar_Tactics_Types.context
                                                            =
                                                            (uu___108_2332.FStar_Tactics_Types.context);
                                                          FStar_Tactics_Types.witness
                                                            = uu____2333;
                                                          FStar_Tactics_Types.goal_ty
                                                            = uu____2334;
                                                          FStar_Tactics_Types.opts
                                                            =
                                                            (uu___108_2332.FStar_Tactics_Types.opts);
                                                          FStar_Tactics_Types.is_guard
                                                            = false
                                                        } in
                                                      [uu____2331] in
                                                    add_goals uu____2328))
                                        | uu____2335 -> ret ()))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2393 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2393 with
           | (tm1,typ,guard) ->
               let uu____2405 =
                 let uu____2408 =
                   let uu____2411 = __apply uopt tm1 typ in
                   bind uu____2411
                     (fun uu____2415  ->
                        add_goal_from_guard goal.FStar_Tactics_Types.context
                          guard goal.FStar_Tactics_Types.opts) in
                 focus uu____2408 in
               let uu____2416 =
                 let uu____2419 = FStar_Syntax_Print.term_to_string tm1 in
                 let uu____2420 = FStar_Syntax_Print.term_to_string typ in
                 let uu____2421 =
                   FStar_Syntax_Print.term_to_string
                     goal.FStar_Tactics_Types.goal_ty in
                 fail3
                   "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                   uu____2419 uu____2420 uu____2421 in
               try_unif uu____2405 uu____2416)
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2430 =
      let is_unit_t t =
        let uu____2437 =
          let uu____2438 = FStar_Syntax_Subst.compress t in
          uu____2438.FStar_Syntax_Syntax.n in
        match uu____2437 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
            true
        | uu____2442 -> false in
      bind cur_goal
        (fun goal  ->
           let uu____2452 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2452 with
           | (tm1,t,guard) ->
               let uu____2464 = FStar_Syntax_Util.arrow_formals_comp t in
               (match uu____2464 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2494 =
                         FStar_List.fold_left
                           (fun uu____2540  ->
                              fun uu____2541  ->
                                match (uu____2540, uu____2541) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2644 = is_unit_t b_t in
                                    if uu____2644
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____2682 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.FStar_Tactics_Types.context
                                           b_t in
                                       match uu____2682 with
                                       | (u,uu____2712,g_u) ->
                                           let uu____2726 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____2726,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2494 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____2796 =
                             let uu____2805 =
                               let uu____2814 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____2814.FStar_Syntax_Syntax.effect_args in
                             match uu____2805 with
                             | pre::post::uu____2825 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____2866 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____2796 with
                            | (pre,post) ->
                                let uu____2895 =
                                  let uu____2896 =
                                    let uu____2897 =
                                      FStar_Syntax_Util.mk_squash post in
                                    FStar_TypeChecker_Rel.teq_nosmt
                                      goal.FStar_Tactics_Types.context
                                      uu____2897
                                      goal.FStar_Tactics_Types.goal_ty in
                                  Prims.op_Negation uu____2896 in
                                if uu____2895
                                then
                                  let uu____2900 =
                                    FStar_Syntax_Print.term_to_string tm1 in
                                  let uu____2901 =
                                    let uu____2902 =
                                      FStar_Syntax_Util.mk_squash post in
                                    FStar_Syntax_Print.term_to_string
                                      uu____2902 in
                                  let uu____2903 =
                                    FStar_Syntax_Print.term_to_string
                                      goal.FStar_Tactics_Types.goal_ty in
                                  fail3
                                    "apply: Cannot instantiate lemma %s (with postcondition %s) to match goal (%s)"
                                    uu____2900 uu____2901 uu____2903
                                else
                                  (let solution =
                                     let uu____2906 =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       goal.FStar_Tactics_Types.context
                                       uu____2906 in
                                   let implicits1 =
                                     FStar_All.pipe_right
                                       implicits.FStar_TypeChecker_Env.implicits
                                       (FStar_List.filter
                                          (fun uu____2974  ->
                                             match uu____2974 with
                                             | (uu____2987,uu____2988,uu____2989,tm2,uu____2991,uu____2992)
                                                 ->
                                                 let uu____2993 =
                                                   FStar_Syntax_Util.head_and_args
                                                     tm2 in
                                                 (match uu____2993 with
                                                  | (hd1,uu____3009) ->
                                                      let uu____3030 =
                                                        let uu____3031 =
                                                          FStar_Syntax_Subst.compress
                                                            hd1 in
                                                        uu____3031.FStar_Syntax_Syntax.n in
                                                      (match uu____3030 with
                                                       | FStar_Syntax_Syntax.Tm_uvar
                                                           uu____3034 -> true
                                                       | uu____3051 -> false)))) in
                                   solve goal solution;
                                   (let uu____3053 = add_implicits implicits1 in
                                    bind uu____3053
                                      (fun uu____3057  ->
                                         bind dismiss
                                           (fun uu____3066  ->
                                              let is_free_uvar uv t1 =
                                                let free_uvars =
                                                  let uu____3077 =
                                                    let uu____3084 =
                                                      FStar_Syntax_Free.uvars
                                                        t1 in
                                                    FStar_Util.set_elements
                                                      uu____3084 in
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.fst
                                                    uu____3077 in
                                                FStar_List.existsML
                                                  (fun u  ->
                                                     FStar_Syntax_Unionfind.equiv
                                                       u uv) free_uvars in
                                              let appears uv goals =
                                                FStar_List.existsML
                                                  (fun g'  ->
                                                     is_free_uvar uv
                                                       g'.FStar_Tactics_Types.goal_ty)
                                                  goals in
                                              let checkone t1 goals =
                                                let uu____3125 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t1 in
                                                match uu____3125 with
                                                | (hd1,uu____3141) ->
                                                    (match hd1.FStar_Syntax_Syntax.n
                                                     with
                                                     | FStar_Syntax_Syntax.Tm_uvar
                                                         (uv,uu____3163) ->
                                                         appears uv goals
                                                     | uu____3188 -> false) in
                                              let sub_goals =
                                                FStar_All.pipe_right
                                                  implicits1
                                                  (FStar_List.map
                                                     (fun uu____3230  ->
                                                        match uu____3230 with
                                                        | (_msg,_env,_uvar,term,typ,uu____3248)
                                                            ->
                                                            let uu___111_3249
                                                              = goal in
                                                            let uu____3250 =
                                                              bnorm
                                                                goal.FStar_Tactics_Types.context
                                                                term in
                                                            let uu____3251 =
                                                              bnorm
                                                                goal.FStar_Tactics_Types.context
                                                                typ in
                                                            {
                                                              FStar_Tactics_Types.context
                                                                =
                                                                (uu___111_3249.FStar_Tactics_Types.context);
                                                              FStar_Tactics_Types.witness
                                                                = uu____3250;
                                                              FStar_Tactics_Types.goal_ty
                                                                = uu____3251;
                                                              FStar_Tactics_Types.opts
                                                                =
                                                                (uu___111_3249.FStar_Tactics_Types.opts);
                                                              FStar_Tactics_Types.is_guard
                                                                =
                                                                (uu___111_3249.FStar_Tactics_Types.is_guard)
                                                            })) in
                                              let rec filter' f xs =
                                                match xs with
                                                | [] -> []
                                                | x::xs1 ->
                                                    let uu____3289 = f x xs1 in
                                                    if uu____3289
                                                    then
                                                      let uu____3292 =
                                                        filter' f xs1 in
                                                      x :: uu____3292
                                                    else filter' f xs1 in
                                              let sub_goals1 =
                                                filter'
                                                  (fun g  ->
                                                     fun goals  ->
                                                       let uu____3306 =
                                                         checkone
                                                           g.FStar_Tactics_Types.witness
                                                           goals in
                                                       Prims.op_Negation
                                                         uu____3306)
                                                  sub_goals in
                                              let uu____3307 =
                                                add_goal_from_guard
                                                  goal.FStar_Tactics_Types.context
                                                  guard
                                                  goal.FStar_Tactics_Types.opts in
                                              bind uu____3307
                                                (fun uu____3312  ->
                                                   let uu____3313 =
                                                     add_irrelevant_goal
                                                       goal.FStar_Tactics_Types.context
                                                       pre
                                                       goal.FStar_Tactics_Types.opts in
                                                   bind uu____3313
                                                     (fun uu____3318  ->
                                                        let uu____3319 =
                                                          trytac trivial in
                                                        bind uu____3319
                                                          (fun uu____3327  ->
                                                             add_goals
                                                               sub_goals1))))))))))) in
    focus uu____2430
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3346 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3346 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3356::(e1,uu____3358)::(e2,uu____3360)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3419 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3442 = destruct_eq' typ in
    match uu____3442 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3472 = FStar_Syntax_Util.un_squash typ in
        (match uu____3472 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3505 =
           FStar_All.pipe_left mlog
             (fun uu____3515  ->
                let uu____3516 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3517 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3516
                  uu____3517) in
         bind uu____3505
           (fun uu____3525  ->
              let uu____3526 =
                let uu____3533 =
                  let uu____3534 =
                    FStar_TypeChecker_Env.lookup_bv
                      goal.FStar_Tactics_Types.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3534 in
                destruct_eq uu____3533 in
              match uu____3526 with
              | FStar_Pervasives_Native.Some (x,e) ->
                  let uu____3551 =
                    let uu____3552 = FStar_Syntax_Subst.compress x in
                    uu____3552.FStar_Syntax_Syntax.n in
                  (match uu____3551 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___112_3559 = goal in
                         let uu____3560 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)]
                             goal.FStar_Tactics_Types.witness in
                         let uu____3561 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)]
                             goal.FStar_Tactics_Types.goal_ty in
                         {
                           FStar_Tactics_Types.context =
                             (uu___112_3559.FStar_Tactics_Types.context);
                           FStar_Tactics_Types.witness = uu____3560;
                           FStar_Tactics_Types.goal_ty = uu____3561;
                           FStar_Tactics_Types.opts =
                             (uu___112_3559.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___112_3559.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur goal1
                   | uu____3562 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3563 -> fail "Not an equality hypothesis"))
let subst_goal:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal
  =
  fun b1  ->
    fun b2  ->
      fun s  ->
        fun g  ->
          let rec alpha e =
            let uu____3594 = FStar_TypeChecker_Env.pop_bv e in
            match uu____3594 with
            | FStar_Pervasives_Native.None  -> e
            | FStar_Pervasives_Native.Some (bv,e') ->
                if FStar_Syntax_Syntax.bv_eq bv b1
                then FStar_TypeChecker_Env.push_bv e' b2
                else
                  (let uu____3612 = alpha e' in
                   let uu____3613 =
                     let uu___113_3614 = bv in
                     let uu____3615 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___113_3614.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___113_3614.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3615
                     } in
                   FStar_TypeChecker_Env.push_bv uu____3612 uu____3613) in
          let c = alpha g.FStar_Tactics_Types.context in
          let w = FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
          let t = FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
          let uu___114_3621 = g in
          {
            FStar_Tactics_Types.context = c;
            FStar_Tactics_Types.witness = w;
            FStar_Tactics_Types.goal_ty = t;
            FStar_Tactics_Types.opts =
              (uu___114_3621.FStar_Tactics_Types.opts);
            FStar_Tactics_Types.is_guard =
              (uu___114_3621.FStar_Tactics_Types.is_guard)
          }
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3642 = b in
           match uu____3642 with
           | (bv,uu____3646) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___115_3650 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___115_3650.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___115_3650.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3654 =
                   let uu____3655 =
                     let uu____3662 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3662) in
                   FStar_Syntax_Syntax.NT uu____3655 in
                 [uu____3654] in
               let uu____3663 = subst_goal bv bv' s1 goal in
               replace_cur uu____3663)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3669 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____3669 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____3691 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____3691 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___116_3725 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___116_3725.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___116_3725.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3737 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____3737 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____3758 = FStar_Syntax_Print.bv_to_string x in
               let uu____3759 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____3758 uu____3759
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3766 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____3766 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____3788 = FStar_Util.set_mem x fns_ty in
           if uu____3788
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____3792 = new_uvar env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____3792
                (fun u  ->
                   let uu____3798 =
                     let uu____3799 = trysolve goal u in
                     Prims.op_Negation uu____3799 in
                   if uu____3798
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___117_3804 = goal in
                        let uu____3805 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____3805;
                          FStar_Tactics_Types.goal_ty =
                            (uu___117_3804.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___117_3804.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___117_3804.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____3807  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____3819 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____3819 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____3843  ->
                    let uu____3844 = clear b in
                    bind uu____3844
                      (fun uu____3848  ->
                         bind intro (fun uu____3850  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___118_3867 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___118_3867.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___118_3867.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___118_3867.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___118_3867.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____3869  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___119_3886 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___119_3886.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___119_3886.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___119_3886.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___119_3886.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____3888  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3930 = f x in
          bind uu____3930
            (fun y  ->
               let uu____3938 = mapM f xs in
               bind uu____3938 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____3984 = FStar_Syntax_Subst.compress t in
          uu____3984.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4019 = ff hd1 in
              bind uu____4019
                (fun hd2  ->
                   let fa uu____4039 =
                     match uu____4039 with
                     | (a,q) ->
                         let uu____4052 = ff a in
                         bind uu____4052 (fun a1  -> ret (a1, q)) in
                   let uu____4065 = mapM fa args in
                   bind uu____4065
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4125 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4125 with
               | (bs1,t') ->
                   let uu____4134 =
                     let uu____4137 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4137 t' in
                   bind uu____4134
                     (fun t''  ->
                        let uu____4141 =
                          let uu____4142 =
                            let uu____4159 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4160 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4159, uu____4160, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4142 in
                        ret uu____4141))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4181 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___120_4185 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___120_4185.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___120_4185.FStar_Syntax_Syntax.vars)
                }))
let pointwise_rec:
  FStar_Tactics_Types.proofstate ->
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
            let uu____4214 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4214 with
            | (t1,lcomp,g) ->
                let uu____4226 =
                  (let uu____4229 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____4229) ||
                    (let uu____4231 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4231) in
                if uu____4226
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4238 = new_uvar env typ in
                   bind uu____4238
                     (fun ut  ->
                        log ps
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
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4256 typ t1 ut in
                           add_irrelevant_goal env uu____4255 opts in
                         bind uu____4252
                           (fun uu____4259  ->
                              let uu____4260 =
                                bind tau
                                  (fun uu____4265  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4260))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4286 =
           match ps.FStar_Tactics_Types.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4286 with
         | (g,gs) ->
             let gt1 = g.FStar_Tactics_Types.goal_ty in
             (log ps
                (fun uu____4323  ->
                   let uu____4324 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4324);
              bind dismiss_all
                (fun uu____4327  ->
                   let uu____4328 =
                     tac_bottom_fold_env
                       (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                       g.FStar_Tactics_Types.context gt1 in
                   bind uu____4328
                     (fun gt'  ->
                        log ps
                          (fun uu____4338  ->
                             let uu____4339 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4339);
                        (let uu____4340 = push_goals gs in
                         bind uu____4340
                           (fun uu____4344  ->
                              add_goals
                                [(let uu___121_4346 = g in
                                  {
                                    FStar_Tactics_Types.context =
                                      (uu___121_4346.FStar_Tactics_Types.context);
                                    FStar_Tactics_Types.witness =
                                      (uu___121_4346.FStar_Tactics_Types.witness);
                                    FStar_Tactics_Types.goal_ty = gt';
                                    FStar_Tactics_Types.opts =
                                      (uu___121_4346.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___121_4346.FStar_Tactics_Types.is_guard)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4366 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____4366 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4378 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4378 with
            | (hd1,args) ->
                let uu____4411 =
                  let uu____4424 =
                    let uu____4425 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4425.FStar_Syntax_Syntax.n in
                  (uu____4424, args) in
                (match uu____4411 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4439::(l,uu____4441)::(r,uu____4443)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4490 =
                       let uu____4491 =
                         FStar_TypeChecker_Rel.teq_nosmt
                           g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____4491 in
                     if uu____4490
                     then
                       let uu____4494 = FStar_Syntax_Print.term_to_string l in
                       let uu____4495 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4494 uu____4495
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____4499) ->
                     let uu____4516 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____4516))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4524 =
         new_uvar g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
       bind uu____4524
         (fun u  ->
            let g' =
              let uu___122_4531 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___122_4531.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___122_4531.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___122_4531.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___122_4531.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____4534  ->
                 let uu____4535 =
                   let uu____4538 =
                     let uu____4539 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4539
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal g.FStar_Tactics_Types.context
                     uu____4538 g.FStar_Tactics_Types.opts in
                 bind uu____4535
                   (fun uu____4542  ->
                      let uu____4543 = add_goals [g'] in
                      bind uu____4543 (fun uu____4547  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___123_4564 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___123_4564.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___123_4564.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___123_4564.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___123_4564.FStar_Tactics_Types.smt_goals)
              })
       | uu____4565 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___124_4580 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___124_4580.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___124_4580.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___124_4580.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___124_4580.FStar_Tactics_Types.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____4587 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____4629 =
           (g.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
             g.FStar_Tactics_Types.context t in
         match uu____4629 with
         | (t1,typ,guard) ->
             let uu____4645 = FStar_Syntax_Util.head_and_args typ in
             (match uu____4645 with
              | (hd1,args) ->
                  let uu____4688 =
                    let uu____4701 =
                      let uu____4702 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____4702.FStar_Syntax_Syntax.n in
                    (uu____4701, args) in
                  (match uu____4688 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____4721)::(q,uu____4723)::[]) when
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
                         let uu___125_4761 = g in
                         let uu____4762 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_p in
                         {
                           FStar_Tactics_Types.context = uu____4762;
                           FStar_Tactics_Types.witness =
                             (uu___125_4761.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___125_4761.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___125_4761.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___125_4761.FStar_Tactics_Types.is_guard)
                         } in
                       let g2 =
                         let uu___126_4764 = g in
                         let uu____4765 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_q in
                         {
                           FStar_Tactics_Types.context = uu____4765;
                           FStar_Tactics_Types.witness =
                             (uu___126_4764.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___126_4764.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___126_4764.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___126_4764.FStar_Tactics_Types.is_guard)
                         } in
                       bind dismiss
                         (fun uu____4772  ->
                            let uu____4773 = add_goals [g1; g2] in
                            bind uu____4773
                              (fun uu____4782  ->
                                 let uu____4783 =
                                   let uu____4788 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____4789 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____4788, uu____4789) in
                                 ret uu____4783))
                   | uu____4794 ->
                       let uu____4807 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____4807)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____4830 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____4830);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___127_4837 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___127_4837.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___127_4837.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___127_4837.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___127_4837.FStar_Tactics_Types.is_guard)
                 } in
               replace_cur g'
           | FStar_Getopt.Error err1 ->
               fail2 "Setting options `%s` failed: %s" s err1
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
let cur_env: FStar_TypeChecker_Env.env tac =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
let cur_goal': FStar_Syntax_Syntax.typ tac =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
let cur_witness: FStar_Syntax_Syntax.term tac =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
let unquote:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ty  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let env =
             FStar_TypeChecker_Env.set_expected_typ
               goal.FStar_Tactics_Types.context ty in
           let uu____4878 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               env tm in
           match uu____4878 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____4907 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____4913 =
              let uu____4914 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4914 in
            new_uvar env uu____4913 in
      bind uu____4907
        (fun typ  ->
           let uu____4926 = new_uvar env typ in
           bind uu____4926 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____4946 =
             FStar_TypeChecker_Rel.teq_nosmt
               ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____4946)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____4966  ->
             let uu____4967 = FStar_Options.unsafe_tactic_exec () in
             if uu____4967
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____4973  -> fun uu____4974  -> false) in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
let goal_of_goal_ty:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____4996 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____4996 with
      | (u,uu____5014,g_u) ->
          let g =
            let uu____5029 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5029;
              FStar_Tactics_Types.is_guard = false
            } in
          (g, g_u)
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____5046 = goal_of_goal_ty env typ in
      match uu____5046 with
      | (g,g_u) ->
          let ps =
            {
              FStar_Tactics_Types.main_context = env;
              FStar_Tactics_Types.main_goal = g;
              FStar_Tactics_Types.all_implicits =
                (g_u.FStar_TypeChecker_Env.implicits);
              FStar_Tactics_Types.goals = [g];
              FStar_Tactics_Types.smt_goals = []
            } in
          (ps, (g.FStar_Tactics_Types.witness))