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
  'Auu____88 .
    'Auu____88 tac ->
      FStar_Tactics_Types.proofstate ->
        'Auu____88 FStar_Tactics_Result.__result
  = fun t  -> fun p  -> t.tac_f p
let ret: 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p))
let bind: 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____155 = run t1 p in
           match uu____155 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____162 = t2 a in run uu____162 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: FStar_Tactics_Types.goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____174 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____174
        (FStar_Syntax_Print.binders_to_string ", ") in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
    let uu____177 =
      FStar_TypeChecker_Normalize.term_to_string
        g.FStar_Tactics_Types.context w in
    let uu____178 =
      FStar_TypeChecker_Normalize.term_to_string
        g.FStar_Tactics_Types.context t in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____177 uu____178
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____191 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____191
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____204 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____204
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____221 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____221
let comp_to_typ: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____227) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____237) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: FStar_Tactics_Types.goal -> Prims.bool =
  fun g  ->
    let uu____251 =
      let uu____256 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty in
      FStar_Syntax_Util.un_squash uu____256 in
    match uu____251 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____262 -> false
let dump_goal:
  'Auu____273 . 'Auu____273 -> FStar_Tactics_Types.goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____283 = goal_to_string goal in tacprint uu____283
let dump_cur: FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____293 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____297 = FStar_List.hd ps.FStar_Tactics_Types.goals in
            dump_goal ps uu____297))
let ps_to_string:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu____305  ->
    match uu____305 with
    | (msg,ps) ->
        let uu____312 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.goals) in
        let uu____313 =
          let uu____314 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.goals in
          FStar_String.concat "\n" uu____314 in
        let uu____317 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.smt_goals) in
        let uu____318 =
          let uu____319 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.smt_goals in
          FStar_String.concat "\n" uu____319 in
        FStar_Util.format5
          "State dump (%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s" msg
          uu____312 uu____313 uu____317 uu____318
let goal_to_json: FStar_Tactics_Types.goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____327 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____327 FStar_Syntax_Print.binders_to_json in
    let uu____328 =
      let uu____335 =
        let uu____342 =
          let uu____347 =
            let uu____348 =
              let uu____355 =
                let uu____360 =
                  let uu____361 =
                    FStar_TypeChecker_Normalize.term_to_string
                      g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness in
                  FStar_Util.JsonStr uu____361 in
                ("witness", uu____360) in
              let uu____362 =
                let uu____369 =
                  let uu____374 =
                    let uu____375 =
                      FStar_TypeChecker_Normalize.term_to_string
                        g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty in
                    FStar_Util.JsonStr uu____375 in
                  ("type", uu____374) in
                [uu____369] in
              uu____355 :: uu____362 in
            FStar_Util.JsonAssoc uu____348 in
          ("goal", uu____347) in
        [uu____342] in
      ("hyps", g_binders) :: uu____335 in
    FStar_Util.JsonAssoc uu____328
let ps_to_json:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____407  ->
    match uu____407 with
    | (msg,ps) ->
        let uu____414 =
          let uu____421 =
            let uu____428 =
              let uu____433 =
                let uu____434 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals in
                FStar_Util.JsonList uu____434 in
              ("goals", uu____433) in
            let uu____437 =
              let uu____444 =
                let uu____449 =
                  let uu____450 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals in
                  FStar_Util.JsonList uu____450 in
                ("smt-goals", uu____449) in
              [uu____444] in
            uu____428 :: uu____437 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____421 in
        FStar_Util.JsonAssoc uu____414
let dump_proofstate:
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____479  ->
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
      let uu____539 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____539 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____561 =
              let uu____564 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____564 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____561);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail: 'Auu____604 . Prims.string -> 'Auu____604 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____615 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____615
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____623 . Prims.string -> Prims.string -> 'Auu____623 tac =
  fun msg  ->
    fun x  -> let uu____634 = FStar_Util.format1 msg x in fail uu____634
let fail2:
  'Auu____643 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____643 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____658 = FStar_Util.format2 msg x y in fail uu____658
let fail3:
  'Auu____669 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____669 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____688 = FStar_Util.format3 msg x y z in fail uu____688
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____716 = run t ps in
         match uu____716 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success
                ((FStar_Pervasives_Native.Some a), q))
         | FStar_Tactics_Result.Failed (uu____730,uu____731) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____746  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____764 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____778 =
         let uu___90_779 = p in
         let uu____780 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___90_779.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___90_779.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___90_779.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____780;
           FStar_Tactics_Types.smt_goals =
             (uu___90_779.FStar_Tactics_Types.smt_goals)
         } in
       set uu____778)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____795 = trysolve goal solution in
      if uu____795
      then dismiss
      else
        (let uu____799 =
           let uu____800 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____801 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____802 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____800 uu____801
             uu____802 in
         fail uu____799)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___91_809 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___91_809.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___91_809.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___91_809.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___91_809.FStar_Tactics_Types.smt_goals)
          }))
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___92_826 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___92_826.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___92_826.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___92_826.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___92_826.FStar_Tactics_Types.smt_goals)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___93_843 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___93_843.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___93_843.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___93_843.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___93_843.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___94_860 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___94_860.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___94_860.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___94_860.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___94_860.FStar_Tactics_Types.smt_goals)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___95_877 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___95_877.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___95_877.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___95_877.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___95_877.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____887  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___96_900 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___96_900.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___96_900.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___96_900.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___96_900.FStar_Tactics_Types.smt_goals)
            }))
let new_uvar: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun typ  ->
      let uu____925 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____925 with
      | (u,uu____941,g_u) ->
          let uu____955 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____955 (fun uu____959  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____964 = FStar_Syntax_Util.un_squash t in
    match uu____964 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____974 =
          let uu____975 = FStar_Syntax_Subst.compress t' in
          uu____975.FStar_Syntax_Syntax.n in
        (match uu____974 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____979 -> false)
    | uu____980 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____989 = FStar_Syntax_Util.un_squash t in
    match uu____989 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____999 =
          let uu____1000 = FStar_Syntax_Subst.compress t' in
          uu____1000.FStar_Syntax_Syntax.n in
        (match uu____999 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1004 -> false)
    | uu____1005 -> false
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
        let uu____1039 = new_uvar env typ in
        bind uu____1039
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
        let uu____1062 = mk_irrelevant_goal env phi opts in
        bind uu____1062 (fun goal  -> add_goals [goal])
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
       let uu____1084 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1084
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1088 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1088))
let add_goal_from_guard:
  env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Options.optionstate -> Prims.unit tac
  =
  fun e  ->
    fun g  ->
      fun opts  ->
        let uu____1105 =
          let uu____1106 = FStar_TypeChecker_Rel.simplify_guard e g in
          uu____1106.FStar_TypeChecker_Env.guard_f in
        match uu____1105 with
        | FStar_TypeChecker_Common.Trivial  -> ret ()
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____1110 = istrivial e f in
            if uu____1110
            then ret ()
            else
              (let uu____1114 = mk_irrelevant_goal e f opts in
               bind uu____1114
                 (fun goal  ->
                    let goal1 =
                      let uu___97_1121 = goal in
                      {
                        FStar_Tactics_Types.context =
                          (uu___97_1121.FStar_Tactics_Types.context);
                        FStar_Tactics_Types.witness =
                          (uu___97_1121.FStar_Tactics_Types.witness);
                        FStar_Tactics_Types.goal_ty =
                          (uu___97_1121.FStar_Tactics_Types.goal_ty);
                        FStar_Tactics_Types.opts =
                          (uu___97_1121.FStar_Tactics_Types.opts);
                        FStar_Tactics_Types.is_guard = true
                      } in
                    push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1127 = is_irrelevant g in
       if uu____1127
       then bind dismiss (fun uu____1131  -> add_smt_goals [g])
       else
         (let uu____1133 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1133))
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
             let uu____1179 =
               try
                 let uu____1213 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1213
               with | uu____1243 -> fail "divide: not enough goals" in
             bind uu____1179
               (fun uu____1270  ->
                  match uu____1270 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___98_1296 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___98_1296.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___98_1296.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___98_1296.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = []
                        } in
                      let rp =
                        let uu___99_1298 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___99_1298.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___99_1298.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___99_1298.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = []
                        } in
                      let uu____1299 = set lp in
                      bind uu____1299
                        (fun uu____1307  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1321 = set rp in
                                     bind uu____1321
                                       (fun uu____1329  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___100_1345 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___100_1345.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___100_1345.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___100_1345.FStar_Tactics_Types.all_implicits);
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
                                                    let uu____1346 = set p' in
                                                    bind uu____1346
                                                      (fun uu____1354  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1374 = divide (Prims.parse_int "1") f idtac in
    bind uu____1374
      (fun uu____1387  -> match uu____1387 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1422::uu____1423 ->
             let uu____1426 =
               let uu____1435 = map tau in
               divide (Prims.parse_int "1") tau uu____1435 in
             bind uu____1426
               (fun uu____1453  ->
                  match uu____1453 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1492 =
        bind t1
          (fun uu____1497  ->
             let uu____1498 = map t2 in
             bind uu____1498 (fun uu____1506  -> ret ())) in
      focus uu____1492
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1517 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1517 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1532 =
             let uu____1533 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1533 in
           if uu____1532
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1539 = new_uvar env' typ' in
              bind uu____1539
                (fun u  ->
                   let uu____1546 =
                     let uu____1547 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1547 in
                   if uu____1546
                   then
                     let uu____1550 =
                       let uu____1553 =
                         let uu___103_1554 = goal in
                         let uu____1555 = bnorm env' u in
                         let uu____1556 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1555;
                           FStar_Tactics_Types.goal_ty = uu____1556;
                           FStar_Tactics_Types.opts =
                             (uu___103_1554.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___103_1554.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1553 in
                     bind uu____1550 (fun uu____1558  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1564 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1564)
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
       (let uu____1585 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1585 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1604 =
              let uu____1605 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1605 in
            if uu____1604
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1621 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1621; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1623 =
                 let uu____1626 = comp_to_typ c in new_uvar env' uu____1626 in
               bind uu____1623
                 (fun u  ->
                    let lb =
                      let uu____1642 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____1642 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1646 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1646 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____1683 =
                            let uu____1686 =
                              let uu___104_1687 = goal in
                              let uu____1688 = bnorm env' u in
                              let uu____1689 =
                                let uu____1690 = comp_to_typ c in
                                bnorm env' uu____1690 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____1688;
                                FStar_Tactics_Types.goal_ty = uu____1689;
                                FStar_Tactics_Types.opts =
                                  (uu___104_1687.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___104_1687.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____1686 in
                          bind uu____1683
                            (fun uu____1697  ->
                               let uu____1698 =
                                 let uu____1703 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____1703, b) in
                               ret uu____1698)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____1717 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1717))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____1742 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1742 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___105_1749 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___105_1749.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___105_1749.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___105_1749.FStar_Tactics_Types.is_guard)
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
             let uu____1773 = FStar_TypeChecker_Normalize.tr_norm_steps s in
             FStar_List.append
               [FStar_TypeChecker_Normalize.Reify;
               FStar_TypeChecker_Normalize.UnfoldTac] uu____1773 in
           let t1 = normalize steps ps.FStar_Tactics_Types.main_context t in
           ret t1)
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1788 =
           try
             let uu____1816 =
               (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
                 goal.FStar_Tactics_Types.context t in
             ret uu____1816
           with
           | e ->
               let uu____1843 = FStar_Syntax_Print.term_to_string t in
               let uu____1844 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1843
                 uu____1844 in
         bind uu____1788
           (fun uu____1862  ->
              match uu____1862 with
              | (t1,typ,guard) ->
                  let uu____1874 =
                    let uu____1875 =
                      let uu____1876 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1876 in
                    Prims.op_Negation uu____1875 in
                  if uu____1874
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1880 =
                       do_unify goal.FStar_Tactics_Types.context typ
                         goal.FStar_Tactics_Types.goal_ty in
                     if uu____1880
                     then solve goal t1
                     else
                       (let uu____1884 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context t1 in
                        let uu____1885 =
                          let uu____1886 =
                            bnorm goal.FStar_Tactics_Types.context typ in
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context uu____1886 in
                        let uu____1887 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context
                            goal.FStar_Tactics_Types.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1884 uu____1885 uu____1887))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  -> let uu____1896 = __exact t in focus uu____1896
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1910 =
           try
             let uu____1938 =
               FStar_TypeChecker_TcTerm.tc_term
                 goal.FStar_Tactics_Types.context t in
             ret uu____1938
           with
           | e ->
               let uu____1965 = FStar_Syntax_Print.term_to_string t in
               let uu____1966 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1965
                 uu____1966 in
         bind uu____1910
           (fun uu____1984  ->
              match uu____1984 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2002 =
                       let uu____2003 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2003 in
                     if uu____2002
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2007 =
                          let uu____2016 =
                            let uu____2025 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2025.FStar_Syntax_Syntax.effect_args in
                          match uu____2016 with
                          | pre::post::uu____2036 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2077 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2007 with
                        | (pre,post) ->
                            let uu____2106 =
                              do_unify goal.FStar_Tactics_Types.context post
                                goal.FStar_Tactics_Types.goal_ty in
                            if uu____2106
                            then
                              let uu____2109 = solve goal t1 in
                              bind uu____2109
                                (fun uu____2113  ->
                                   add_irrelevant_goal
                                     goal.FStar_Tactics_Types.context pre
                                     goal.FStar_Tactics_Types.opts)
                            else
                              (let uu____2115 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context t1 in
                               let uu____2116 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context post in
                               let uu____2117 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2115 uu____2116 uu____2117)))))
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2130 =
             let uu____2137 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2137 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2130 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2164 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2184 =
               let uu____2189 = __exact tm in trytac uu____2189 in
             bind uu____2184
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2202 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2202 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           let uu____2232 =
                             let uu____2233 =
                               FStar_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu____2233 in
                           if uu____2232
                           then fail "apply: not total codomain"
                           else
                             (let uu____2237 =
                                new_uvar goal.FStar_Tactics_Types.context
                                  bv.FStar_Syntax_Syntax.sort in
                              bind uu____2237
                                (fun u  ->
                                   let tm' =
                                     FStar_Syntax_Syntax.mk_Tm_app tm
                                       [(u, aq)] FStar_Pervasives_Native.None
                                       (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                   let typ' =
                                     let uu____2257 = comp_to_typ c in
                                     FStar_All.pipe_left
                                       (FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.NT (bv, u)])
                                       uu____2257 in
                                   let uu____2258 = __apply uopt tm' typ' in
                                   bind uu____2258
                                     (fun uu____2266  ->
                                        let u1 =
                                          bnorm
                                            goal.FStar_Tactics_Types.context
                                            u in
                                        let uu____2268 =
                                          let uu____2269 =
                                            let uu____2272 =
                                              let uu____2273 =
                                                FStar_Syntax_Util.head_and_args
                                                  u1 in
                                              FStar_Pervasives_Native.fst
                                                uu____2273 in
                                            FStar_Syntax_Subst.compress
                                              uu____2272 in
                                          uu____2269.FStar_Syntax_Syntax.n in
                                        match uu____2268 with
                                        | FStar_Syntax_Syntax.Tm_uvar
                                            (uvar,uu____2301) ->
                                            bind get
                                              (fun ps  ->
                                                 let uu____2329 =
                                                   uopt &&
                                                     (uvar_free uvar ps) in
                                                 if uu____2329
                                                 then ret ()
                                                 else
                                                   (let uu____2333 =
                                                      let uu____2336 =
                                                        let uu___110_2337 =
                                                          goal in
                                                        let uu____2338 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            u1 in
                                                        let uu____2339 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          FStar_Tactics_Types.context
                                                            =
                                                            (uu___110_2337.FStar_Tactics_Types.context);
                                                          FStar_Tactics_Types.witness
                                                            = uu____2338;
                                                          FStar_Tactics_Types.goal_ty
                                                            = uu____2339;
                                                          FStar_Tactics_Types.opts
                                                            =
                                                            (uu___110_2337.FStar_Tactics_Types.opts);
                                                          FStar_Tactics_Types.is_guard
                                                            = false
                                                        } in
                                                      [uu____2336] in
                                                    add_goals uu____2333))
                                        | t -> ret ()))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2398 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2398 with
           | (tm1,typ,guard) ->
               let uu____2410 =
                 let uu____2413 =
                   let uu____2416 = __apply uopt tm1 typ in
                   bind uu____2416
                     (fun uu____2420  ->
                        add_goal_from_guard goal.FStar_Tactics_Types.context
                          guard goal.FStar_Tactics_Types.opts) in
                 focus uu____2413 in
               let uu____2421 =
                 let uu____2424 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context tm1 in
                 let uu____2425 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context typ in
                 let uu____2426 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context
                     goal.FStar_Tactics_Types.goal_ty in
                 fail3
                   "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                   uu____2424 uu____2425 uu____2426 in
               try_unif uu____2410 uu____2421)
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2435 =
      let is_unit_t t =
        let uu____2442 =
          let uu____2443 = FStar_Syntax_Subst.compress t in
          uu____2443.FStar_Syntax_Syntax.n in
        match uu____2442 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
            true
        | uu____2447 -> false in
      bind cur_goal
        (fun goal  ->
           let uu____2457 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2457 with
           | (tm1,t,guard) ->
               let uu____2469 = FStar_Syntax_Util.arrow_formals_comp t in
               (match uu____2469 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2499 =
                         FStar_List.fold_left
                           (fun uu____2545  ->
                              fun uu____2546  ->
                                match (uu____2545, uu____2546) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2649 = is_unit_t b_t in
                                    if uu____2649
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____2687 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.FStar_Tactics_Types.context
                                           b_t in
                                       match uu____2687 with
                                       | (u,uu____2717,g_u) ->
                                           let uu____2731 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____2731,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2499 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____2801 =
                             let uu____2810 =
                               let uu____2819 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____2819.FStar_Syntax_Syntax.effect_args in
                             match uu____2810 with
                             | pre::post::uu____2830 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____2871 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____2801 with
                            | (pre,post) ->
                                let uu____2900 =
                                  let uu____2901 =
                                    let uu____2902 =
                                      FStar_Syntax_Util.mk_squash post in
                                    do_unify goal.FStar_Tactics_Types.context
                                      uu____2902
                                      goal.FStar_Tactics_Types.goal_ty in
                                  Prims.op_Negation uu____2901 in
                                if uu____2900
                                then
                                  let uu____2905 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context tm1 in
                                  let uu____2906 =
                                    let uu____2907 =
                                      FStar_Syntax_Util.mk_squash post in
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context
                                      uu____2907 in
                                  let uu____2908 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context
                                      goal.FStar_Tactics_Types.goal_ty in
                                  fail3
                                    "apply_lemma: Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                    uu____2905 uu____2906 uu____2908
                                else
                                  (let solution =
                                     let uu____2911 =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       goal.FStar_Tactics_Types.context
                                       uu____2911 in
                                   let implicits1 =
                                     FStar_All.pipe_right
                                       implicits.FStar_TypeChecker_Env.implicits
                                       (FStar_List.filter
                                          (fun uu____2979  ->
                                             match uu____2979 with
                                             | (uu____2992,uu____2993,uu____2994,tm2,uu____2996,uu____2997)
                                                 ->
                                                 let uu____2998 =
                                                   FStar_Syntax_Util.head_and_args
                                                     tm2 in
                                                 (match uu____2998 with
                                                  | (hd1,uu____3014) ->
                                                      let uu____3035 =
                                                        let uu____3036 =
                                                          FStar_Syntax_Subst.compress
                                                            hd1 in
                                                        uu____3036.FStar_Syntax_Syntax.n in
                                                      (match uu____3035 with
                                                       | FStar_Syntax_Syntax.Tm_uvar
                                                           uu____3039 -> true
                                                       | uu____3056 -> false)))) in
                                   let uu____3057 = solve goal solution in
                                   bind uu____3057
                                     (fun uu____3062  ->
                                        let uu____3063 =
                                          add_implicits implicits1 in
                                        bind uu____3063
                                          (fun uu____3074  ->
                                             let is_free_uvar uv t1 =
                                               let free_uvars =
                                                 let uu____3085 =
                                                   let uu____3092 =
                                                     FStar_Syntax_Free.uvars
                                                       t1 in
                                                   FStar_Util.set_elements
                                                     uu____3092 in
                                                 FStar_List.map
                                                   FStar_Pervasives_Native.fst
                                                   uu____3085 in
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
                                               let uu____3133 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t1 in
                                               match uu____3133 with
                                               | (hd1,uu____3149) ->
                                                   (match hd1.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_uvar
                                                        (uv,uu____3171) ->
                                                        appears uv goals
                                                    | uu____3196 -> false) in
                                             let sub_goals =
                                               FStar_All.pipe_right
                                                 implicits1
                                                 (FStar_List.map
                                                    (fun uu____3238  ->
                                                       match uu____3238 with
                                                       | (_msg,_env,_uvar,term,typ,uu____3256)
                                                           ->
                                                           let uu___113_3257
                                                             = goal in
                                                           let uu____3258 =
                                                             bnorm
                                                               goal.FStar_Tactics_Types.context
                                                               term in
                                                           let uu____3259 =
                                                             bnorm
                                                               goal.FStar_Tactics_Types.context
                                                               typ in
                                                           {
                                                             FStar_Tactics_Types.context
                                                               =
                                                               (uu___113_3257.FStar_Tactics_Types.context);
                                                             FStar_Tactics_Types.witness
                                                               = uu____3258;
                                                             FStar_Tactics_Types.goal_ty
                                                               = uu____3259;
                                                             FStar_Tactics_Types.opts
                                                               =
                                                               (uu___113_3257.FStar_Tactics_Types.opts);
                                                             FStar_Tactics_Types.is_guard
                                                               =
                                                               (uu___113_3257.FStar_Tactics_Types.is_guard)
                                                           })) in
                                             let rec filter' f xs =
                                               match xs with
                                               | [] -> []
                                               | x::xs1 ->
                                                   let uu____3297 = f x xs1 in
                                                   if uu____3297
                                                   then
                                                     let uu____3300 =
                                                       filter' f xs1 in
                                                     x :: uu____3300
                                                   else filter' f xs1 in
                                             let sub_goals1 =
                                               filter'
                                                 (fun g  ->
                                                    fun goals  ->
                                                      let uu____3314 =
                                                        checkone
                                                          g.FStar_Tactics_Types.witness
                                                          goals in
                                                      Prims.op_Negation
                                                        uu____3314) sub_goals in
                                             let uu____3315 =
                                               add_goal_from_guard
                                                 goal.FStar_Tactics_Types.context
                                                 guard
                                                 goal.FStar_Tactics_Types.opts in
                                             bind uu____3315
                                               (fun uu____3320  ->
                                                  let uu____3321 =
                                                    let uu____3324 =
                                                      let uu____3325 =
                                                        let uu____3326 =
                                                          FStar_Syntax_Util.mk_squash
                                                            pre in
                                                        istrivial
                                                          goal.FStar_Tactics_Types.context
                                                          uu____3326 in
                                                      Prims.op_Negation
                                                        uu____3325 in
                                                    if uu____3324
                                                    then
                                                      add_irrelevant_goal
                                                        goal.FStar_Tactics_Types.context
                                                        pre
                                                        goal.FStar_Tactics_Types.opts
                                                    else ret () in
                                                  bind uu____3321
                                                    (fun uu____3331  ->
                                                       add_goals sub_goals1))))))))) in
    focus uu____2435
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3348 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3348 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3358::(e1,uu____3360)::(e2,uu____3362)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3421 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3444 = destruct_eq' typ in
    match uu____3444 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3474 = FStar_Syntax_Util.un_squash typ in
        (match uu____3474 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let split_env:
  FStar_Syntax_Syntax.bv ->
    env ->
      (env,FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun bvar  ->
    fun e  ->
      let rec aux e1 =
        let uu____3532 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3532 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3580 = aux e' in
               FStar_Util.map_opt uu____3580
                 (fun uu____3604  ->
                    match uu____3604 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3625 = aux e in
      FStar_Util.map_opt uu____3625
        (fun uu____3649  ->
           match uu____3649 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
let push_bvs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env
  =
  fun e  ->
    fun bvs  ->
      FStar_List.fold_right
        (fun b  -> fun e1  -> FStar_TypeChecker_Env.push_bv e1 b) bvs e
let subst_goal:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Tactics_Types.goal ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option
  =
  fun b1  ->
    fun b2  ->
      fun s  ->
        fun g  ->
          let uu____3710 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____3710
            (fun uu____3734  ->
               match uu____3734 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___114_3751 = bv in
                     let uu____3752 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___114_3751.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___114_3751.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3752
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___115_3761 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___115_3761.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___115_3761.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3776 = h in
         match uu____3776 with
         | (bv,uu____3780) ->
             let uu____3781 =
               FStar_All.pipe_left mlog
                 (fun uu____3791  ->
                    let uu____3792 = FStar_Syntax_Print.bv_to_string bv in
                    let uu____3793 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3792
                      uu____3793) in
             bind uu____3781
               (fun uu____3796  ->
                  let uu____3797 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____3797 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____3826 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____3826 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____3841 =
                             let uu____3842 = FStar_Syntax_Subst.compress x in
                             uu____3842.FStar_Syntax_Syntax.n in
                           (match uu____3841 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___116_3855 = bv1 in
                                  let uu____3856 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___116_3855.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___116_3855.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____3856
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____3862 =
                                  let uu___117_3863 = goal in
                                  let uu____3864 = push_bvs e0 (bv :: bvs1) in
                                  let uu____3865 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____3866 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____3864;
                                    FStar_Tactics_Types.witness = uu____3865;
                                    FStar_Tactics_Types.goal_ty = uu____3866;
                                    FStar_Tactics_Types.opts =
                                      (uu___117_3863.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___117_3863.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____3862
                            | uu____3867 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____3868 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3895 = b in
           match uu____3895 with
           | (bv,uu____3899) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___118_3903 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___118_3903.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___118_3903.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3907 =
                   let uu____3908 =
                     let uu____3915 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3915) in
                   FStar_Syntax_Syntax.NT uu____3908 in
                 [uu____3907] in
               let uu____3916 = subst_goal bv bv' s1 goal in
               (match uu____3916 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____3936 = b in
         match uu____3936 with
         | (bv,uu____3940) ->
             let uu____3941 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____3941 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____3970 = FStar_Syntax_Util.type_u () in
                  (match uu____3970 with
                   | (ty,u) ->
                       let uu____3979 = new_uvar e0 ty in
                       bind uu____3979
                         (fun t'  ->
                            let bv'' =
                              let uu___119_3989 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___119_3989.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___119_3989.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____3993 =
                                let uu____3994 =
                                  let uu____4001 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4001) in
                                FStar_Syntax_Syntax.NT uu____3994 in
                              [uu____3993] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___120_4009 = b1 in
                                   let uu____4010 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___120_4009.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___120_4009.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4010
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4016  ->
                                 let uu____4017 =
                                   let uu____4020 =
                                     let uu____4023 =
                                       let uu___121_4024 = goal in
                                       let uu____4025 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4026 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4025;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4026;
                                         FStar_Tactics_Types.opts =
                                           (uu___121_4024.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___121_4024.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4023] in
                                   add_goals uu____4020 in
                                 bind uu____4017
                                   (fun uu____4029  ->
                                      let uu____4030 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal e0 uu____4030
                                        goal.FStar_Tactics_Types.opts))))))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4036 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4036 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4058 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4058 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___122_4092 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___122_4092.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___122_4092.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4104 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4104 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4125 = FStar_Syntax_Print.bv_to_string x in
               let uu____4126 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4125 uu____4126
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4133 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4133 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4155 = FStar_Util.set_mem x fns_ty in
           if uu____4155
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4159 = new_uvar env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4159
                (fun u  ->
                   let uu____4165 =
                     let uu____4166 = trysolve goal u in
                     Prims.op_Negation uu____4166 in
                   if uu____4165
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___123_4171 = goal in
                        let uu____4172 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4172;
                          FStar_Tactics_Types.goal_ty =
                            (uu___123_4171.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___123_4171.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___123_4171.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4174  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4186 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4186 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4210  ->
                    let uu____4211 = clear b in
                    bind uu____4211
                      (fun uu____4215  ->
                         bind intro (fun uu____4217  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___124_4234 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___124_4234.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___124_4234.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___124_4234.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___124_4234.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4236  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___125_4253 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___125_4253.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___125_4253.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___125_4253.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___125_4253.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4255  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4297 = f x in
          bind uu____4297
            (fun y  ->
               let uu____4305 = mapM f xs in
               bind uu____4305 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4351 = FStar_Syntax_Subst.compress t in
          uu____4351.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4386 = ff hd1 in
              bind uu____4386
                (fun hd2  ->
                   let fa uu____4406 =
                     match uu____4406 with
                     | (a,q) ->
                         let uu____4419 = ff a in
                         bind uu____4419 (fun a1  -> ret (a1, q)) in
                   let uu____4432 = mapM fa args in
                   bind uu____4432
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4492 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4492 with
               | (bs1,t') ->
                   let uu____4501 =
                     let uu____4504 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4504 t' in
                   bind uu____4501
                     (fun t''  ->
                        let uu____4508 =
                          let uu____4509 =
                            let uu____4526 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4527 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4526, uu____4527, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4509 in
                        ret uu____4508))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4548 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___126_4552 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___126_4552.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___126_4552.FStar_Syntax_Syntax.vars)
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
            let uu____4581 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4581 with
            | (t1,lcomp,g) ->
                let uu____4593 =
                  (let uu____4596 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____4596) ||
                    (let uu____4598 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4598) in
                if uu____4593
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4605 = new_uvar env typ in
                   bind uu____4605
                     (fun ut  ->
                        log ps
                          (fun uu____4616  ->
                             let uu____4617 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4618 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4617 uu____4618);
                        (let uu____4619 =
                           let uu____4622 =
                             let uu____4623 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4623 typ t1 ut in
                           add_irrelevant_goal env uu____4622 opts in
                         bind uu____4619
                           (fun uu____4626  ->
                              let uu____4627 =
                                bind tau
                                  (fun uu____4632  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4627))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4653 =
           match ps.FStar_Tactics_Types.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4653 with
         | (g,gs) ->
             let gt1 = g.FStar_Tactics_Types.goal_ty in
             (log ps
                (fun uu____4690  ->
                   let uu____4691 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4691);
              bind dismiss_all
                (fun uu____4694  ->
                   let uu____4695 =
                     tac_bottom_fold_env
                       (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                       g.FStar_Tactics_Types.context gt1 in
                   bind uu____4695
                     (fun gt'  ->
                        log ps
                          (fun uu____4705  ->
                             let uu____4706 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4706);
                        (let uu____4707 = push_goals gs in
                         bind uu____4707
                           (fun uu____4711  ->
                              add_goals
                                [(let uu___127_4713 = g in
                                  {
                                    FStar_Tactics_Types.context =
                                      (uu___127_4713.FStar_Tactics_Types.context);
                                    FStar_Tactics_Types.witness =
                                      (uu___127_4713.FStar_Tactics_Types.witness);
                                    FStar_Tactics_Types.goal_ty = gt';
                                    FStar_Tactics_Types.opts =
                                      (uu___127_4713.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___127_4713.FStar_Tactics_Types.is_guard)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4733 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____4733 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4745 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4745 with
            | (hd1,args) ->
                let uu____4778 =
                  let uu____4791 =
                    let uu____4792 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4792.FStar_Syntax_Syntax.n in
                  (uu____4791, args) in
                (match uu____4778 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4806::(l,uu____4808)::(r,uu____4810)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4857 =
                       let uu____4858 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____4858 in
                     if uu____4857
                     then
                       let uu____4861 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____4862 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4861 uu____4862
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____4865) ->
                     let uu____4882 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____4882))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4890 =
         new_uvar g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
       bind uu____4890
         (fun u  ->
            let g' =
              let uu___128_4897 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___128_4897.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___128_4897.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___128_4897.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___128_4897.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____4900  ->
                 let uu____4901 =
                   let uu____4904 =
                     let uu____4905 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4905
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal g.FStar_Tactics_Types.context
                     uu____4904 g.FStar_Tactics_Types.opts in
                 bind uu____4901
                   (fun uu____4908  ->
                      let uu____4909 = add_goals [g'] in
                      bind uu____4909 (fun uu____4913  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___129_4930 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___129_4930.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___129_4930.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___129_4930.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___129_4930.FStar_Tactics_Types.smt_goals)
              })
       | uu____4931 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___130_4946 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___130_4946.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___130_4946.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___130_4946.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___130_4946.FStar_Tactics_Types.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____4953 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____4995 =
           (g.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
             g.FStar_Tactics_Types.context t in
         match uu____4995 with
         | (t1,typ,guard) ->
             let uu____5011 = FStar_Syntax_Util.head_and_args typ in
             (match uu____5011 with
              | (hd1,args) ->
                  let uu____5054 =
                    let uu____5067 =
                      let uu____5068 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____5068.FStar_Syntax_Syntax.n in
                    (uu____5067, args) in
                  (match uu____5054 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____5087)::(q,uu____5089)::[]) when
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
                         let uu___131_5127 = g in
                         let uu____5128 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_p in
                         {
                           FStar_Tactics_Types.context = uu____5128;
                           FStar_Tactics_Types.witness =
                             (uu___131_5127.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___131_5127.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___131_5127.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___131_5127.FStar_Tactics_Types.is_guard)
                         } in
                       let g2 =
                         let uu___132_5130 = g in
                         let uu____5131 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_q in
                         {
                           FStar_Tactics_Types.context = uu____5131;
                           FStar_Tactics_Types.witness =
                             (uu___132_5130.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___132_5130.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___132_5130.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___132_5130.FStar_Tactics_Types.is_guard)
                         } in
                       bind dismiss
                         (fun uu____5138  ->
                            let uu____5139 = add_goals [g1; g2] in
                            bind uu____5139
                              (fun uu____5148  ->
                                 let uu____5149 =
                                   let uu____5154 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____5155 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____5154, uu____5155) in
                                 ret uu____5149))
                   | uu____5160 ->
                       let uu____5173 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context typ in
                       fail1 "Not a disjunction: %s" uu____5173)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5196 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5196);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___133_5203 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___133_5203.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___133_5203.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___133_5203.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___133_5203.FStar_Tactics_Types.is_guard)
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
           let uu____5244 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               env tm in
           match uu____5244 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5273 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5279 =
              let uu____5280 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5280 in
            new_uvar env uu____5279 in
      bind uu____5273
        (fun typ  ->
           let uu____5292 = new_uvar env typ in
           bind uu____5292 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5312 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5312)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5332  ->
             let uu____5333 = FStar_Options.unsafe_tactic_exec () in
             if uu____5333
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5339  -> fun uu____5340  -> false) in
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
      let uu____5362 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5362 with
      | (u,uu____5380,g_u) ->
          let g =
            let uu____5395 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5395;
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
      let uu____5412 = goal_of_goal_ty env typ in
      match uu____5412 with
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