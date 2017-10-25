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
        let uu____312 = FStar_Util.string_of_int ps.FStar_Tactics_Types.depth in
        let uu____313 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.goals) in
        let uu____314 =
          let uu____315 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.goals in
          FStar_String.concat "\n" uu____315 in
        let uu____318 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.smt_goals) in
        let uu____319 =
          let uu____320 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.smt_goals in
          FStar_String.concat "\n" uu____320 in
        FStar_Util.format6
          "State dump @ depth %s(%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s"
          uu____312 msg uu____313 uu____314 uu____318 uu____319
let goal_to_json: FStar_Tactics_Types.goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____328 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____328 FStar_Syntax_Print.binders_to_json in
    let uu____329 =
      let uu____336 =
        let uu____343 =
          let uu____348 =
            let uu____349 =
              let uu____356 =
                let uu____361 =
                  let uu____362 =
                    FStar_TypeChecker_Normalize.term_to_string
                      g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness in
                  FStar_Util.JsonStr uu____362 in
                ("witness", uu____361) in
              let uu____363 =
                let uu____370 =
                  let uu____375 =
                    let uu____376 =
                      FStar_TypeChecker_Normalize.term_to_string
                        g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty in
                    FStar_Util.JsonStr uu____376 in
                  ("type", uu____375) in
                [uu____370] in
              uu____356 :: uu____363 in
            FStar_Util.JsonAssoc uu____349 in
          ("goal", uu____348) in
        [uu____343] in
      ("hyps", g_binders) :: uu____336 in
    FStar_Util.JsonAssoc uu____329
let ps_to_json:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____408  ->
    match uu____408 with
    | (msg,ps) ->
        let uu____415 =
          let uu____422 =
            let uu____429 =
              let uu____434 =
                let uu____435 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals in
                FStar_Util.JsonList uu____435 in
              ("goals", uu____434) in
            let uu____438 =
              let uu____445 =
                let uu____450 =
                  let uu____451 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals in
                  FStar_Util.JsonList uu____451 in
                ("smt-goals", uu____450) in
              [uu____445] in
            uu____429 :: uu____438 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____422 in
        FStar_Util.JsonAssoc uu____415
let dump_proofstate:
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____480  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
let print_proof_state1: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc in
         (let uu____502 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_cur uu____502 msg);
         FStar_Tactics_Result.Success ((), ps))
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc in
         (let uu____519 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_proofstate uu____519 msg);
         FStar_Tactics_Result.Success ((), ps))
let get: FStar_Tactics_Types.proofstate tac =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p))
let tac_verb_dbg: Prims.bool FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let rec log:
  FStar_Tactics_Types.proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit
  =
  fun ps  ->
    fun f  ->
      let uu____550 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____550 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____604 =
              let uu____607 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____607 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____604);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'Auu____697 . Prims.string -> 'Auu____697 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____708 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____708
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____716 . Prims.string -> Prims.string -> 'Auu____716 tac =
  fun msg  ->
    fun x  -> let uu____727 = FStar_Util.format1 msg x in fail uu____727
let fail2:
  'Auu____736 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____736 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____751 = FStar_Util.format2 msg x y in fail uu____751
let fail3:
  'Auu____762 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____762 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____781 = FStar_Util.format3 msg x y z in fail uu____781
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____809 = run t ps in
         match uu____809 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success
                ((FStar_Pervasives_Native.Some a), q))
         | FStar_Tactics_Result.Failed (uu____823,uu____824) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let wrap_err: 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____856 = run t ps in
           match uu____856 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____874  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____892 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____906 =
         let uu___135_907 = p in
         let uu____908 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___135_907.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___135_907.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___135_907.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____908;
           FStar_Tactics_Types.smt_goals =
             (uu___135_907.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___135_907.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___135_907.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___135_907.FStar_Tactics_Types.psc)
         } in
       set uu____906)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____923 = trysolve goal solution in
      if uu____923
      then dismiss
      else
        (let uu____927 =
           let uu____928 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____929 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____930 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____928 uu____929
             uu____930 in
         fail uu____927)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___136_937 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___136_937.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___136_937.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___136_937.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___136_937.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___136_937.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___136_937.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___136_937.FStar_Tactics_Types.psc)
          }))
let check_valid_goal: FStar_Tactics_Types.goal -> Prims.unit =
  fun g  ->
    let b = true in
    let env = g.FStar_Tactics_Types.context in
    let b1 =
      b && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.witness) in
    let b2 =
      b1 && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.goal_ty) in
    let rec aux b3 e =
      let uu____953 = FStar_TypeChecker_Env.pop_bv e in
      match uu____953 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____971 = let uu____972 = aux b2 env in Prims.op_Negation uu____972 in
    if uu____971
    then
      let uu____973 =
        let uu____974 = goal_to_string g in
        FStar_Util.format1
          "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
          uu____974 in
      FStar_Errors.warn
        (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____973
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___137_994 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___137_994.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___137_994.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___137_994.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___137_994.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___137_994.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___137_994.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___137_994.FStar_Tactics_Types.psc)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___138_1013 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___138_1013.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___138_1013.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___138_1013.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___138_1013.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___138_1013.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___138_1013.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___138_1013.FStar_Tactics_Types.psc)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___139_1032 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___139_1032.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___139_1032.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___139_1032.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___139_1032.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___139_1032.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___139_1032.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___139_1032.FStar_Tactics_Types.psc)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___140_1051 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___140_1051.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___140_1051.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___140_1051.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___140_1051.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___140_1051.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___140_1051.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___140_1051.FStar_Tactics_Types.psc)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1061  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___141_1074 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___141_1074.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___141_1074.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___141_1074.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___141_1074.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___141_1074.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___141_1074.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___141_1074.FStar_Tactics_Types.psc)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1103 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1103 with
        | (u,uu____1119,g_u) ->
            let uu____1133 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1133 (fun uu____1137  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1142 = FStar_Syntax_Util.un_squash t in
    match uu____1142 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1152 =
          let uu____1153 = FStar_Syntax_Subst.compress t' in
          uu____1153.FStar_Syntax_Syntax.n in
        (match uu____1152 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1157 -> false)
    | uu____1158 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1167 = FStar_Syntax_Util.un_squash t in
    match uu____1167 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1177 =
          let uu____1178 = FStar_Syntax_Subst.compress t' in
          uu____1178.FStar_Syntax_Syntax.n in
        (match uu____1177 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1182 -> false)
    | uu____1183 -> false
let cur_goal: FStar_Tactics_Types.goal tac =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let mk_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Options.optionstate -> FStar_Tactics_Types.goal tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let typ = FStar_Syntax_Util.mk_squash phi in
          let uu____1221 = new_uvar reason env typ in
          bind uu____1221
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
let __tc:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 tac
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           try
             let uu____1279 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1279
           with | e1 -> fail "not typeable")
let must_trivial: env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1329 =
          let uu____1330 =
            let uu____1331 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1331 in
          Prims.op_Negation uu____1330 in
        if uu____1329 then fail "got non-trivial guard" else ret ()
      with | uu____1340 -> fail "got non-trivial guard"
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1349 =
      bind cur_goal
        (fun goal  ->
           let uu____1355 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1355
             (fun uu____1375  ->
                match uu____1375 with
                | (t1,typ,guard) ->
                    let uu____1387 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____1387 (fun uu____1391  -> ret typ))) in
    FStar_All.pipe_left (wrap_err "tc") uu____1349
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1416 = mk_irrelevant_goal reason env phi opts in
          bind uu____1416 (fun goal  -> add_goals [goal])
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
       let uu____1438 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1438
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1442 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1442))
let add_goal_from_guard:
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t ->
        FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____1463 =
            let uu____1464 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1464.FStar_TypeChecker_Env.guard_f in
          match uu____1463 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1468 = istrivial e f in
              if uu____1468
              then ret ()
              else
                (let uu____1472 = mk_irrelevant_goal reason e f opts in
                 bind uu____1472
                   (fun goal  ->
                      let goal1 =
                        let uu___146_1479 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___146_1479.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___146_1479.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___146_1479.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___146_1479.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard = true
                        } in
                      push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1485 = is_irrelevant g in
       if uu____1485
       then bind dismiss (fun uu____1489  -> add_smt_goals [g])
       else
         (let uu____1491 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1491))
let divide:
  'a 'b .
    FStar_BigInt.t ->
      'a tac -> 'b tac -> ('a,'b) FStar_Pervasives_Native.tuple2 tac
  =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____1537 =
               try
                 let uu____1571 =
                   let uu____1580 = FStar_BigInt.to_int_fs n1 in
                   FStar_List.splitAt uu____1580 p.FStar_Tactics_Types.goals in
                 ret uu____1571
               with | uu____1602 -> fail "divide: not enough goals" in
             bind uu____1537
               (fun uu____1629  ->
                  match uu____1629 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___147_1655 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___147_1655.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___147_1655.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___147_1655.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___147_1655.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___147_1655.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___147_1655.FStar_Tactics_Types.psc)
                        } in
                      let rp =
                        let uu___148_1657 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___148_1657.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___148_1657.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___148_1657.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___148_1657.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___148_1657.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___148_1657.FStar_Tactics_Types.psc)
                        } in
                      let uu____1658 = set lp in
                      bind uu____1658
                        (fun uu____1666  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1680 = set rp in
                                     bind uu____1680
                                       (fun uu____1688  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___149_1704 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___149_1704.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___149_1704.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___149_1704.FStar_Tactics_Types.all_implicits);
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
                                                                p.FStar_Tactics_Types.smt_goals));
                                                        FStar_Tactics_Types.depth
                                                          =
                                                          (uu___149_1704.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___149_1704.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___149_1704.FStar_Tactics_Types.psc)
                                                      } in
                                                    let uu____1705 = set p' in
                                                    bind uu____1705
                                                      (fun uu____1713  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1733 = divide FStar_BigInt.one f idtac in
    bind uu____1733
      (fun uu____1746  -> match uu____1746 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1781::uu____1782 ->
             let uu____1785 =
               let uu____1794 = map tau in
               divide FStar_BigInt.one tau uu____1794 in
             bind uu____1785
               (fun uu____1812  ->
                  match uu____1812 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1851 =
        bind t1
          (fun uu____1856  ->
             let uu____1857 = map t2 in
             bind uu____1857 (fun uu____1865  -> ret ())) in
      focus uu____1851
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1876 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1876 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1891 =
             let uu____1892 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1892 in
           if uu____1891
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1898 = new_uvar "intro" env' typ' in
              bind uu____1898
                (fun u  ->
                   let uu____1905 =
                     let uu____1906 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1906 in
                   if uu____1905
                   then
                     let uu____1909 =
                       let uu____1912 =
                         let uu___152_1913 = goal in
                         let uu____1914 = bnorm env' u in
                         let uu____1915 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1914;
                           FStar_Tactics_Types.goal_ty = uu____1915;
                           FStar_Tactics_Types.opts =
                             (uu___152_1913.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___152_1913.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1912 in
                     bind uu____1909 (fun uu____1917  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1923 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1923)
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
       (let uu____1944 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1944 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1963 =
              let uu____1964 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1964 in
            if uu____1963
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1980 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1980; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1982 =
                 let uu____1985 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____1985 in
               bind uu____1982
                 (fun u  ->
                    let lb =
                      let uu____2001 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2001 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2005 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2005 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2042 =
                            let uu____2045 =
                              let uu___153_2046 = goal in
                              let uu____2047 = bnorm env' u in
                              let uu____2048 =
                                let uu____2049 = comp_to_typ c in
                                bnorm env' uu____2049 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2047;
                                FStar_Tactics_Types.goal_ty = uu____2048;
                                FStar_Tactics_Types.opts =
                                  (uu___153_2046.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___153_2046.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2045 in
                          bind uu____2042
                            (fun uu____2056  ->
                               let uu____2057 =
                                 let uu____2062 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2062, b) in
                               ret uu____2057)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2076 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2076))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2101 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2101 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___154_2108 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___154_2108.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___154_2108.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___154_2108.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2129 =
          bind get
            (fun ps  ->
               let uu____2135 = __tc e t in
               bind uu____2135
                 (fun uu____2157  ->
                    match uu____2157 with
                    | (t1,uu____2167,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2173 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2173 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2129
let __exact: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun force_guard  ->
    fun t  ->
      bind cur_goal
        (fun goal  ->
           let uu____2196 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____2196
             (fun uu____2216  ->
                match uu____2216 with
                | (t1,typ,guard) ->
                    let uu____2228 =
                      if force_guard
                      then
                        must_trivial goal.FStar_Tactics_Types.context guard
                      else
                        add_goal_from_guard "__exact typing"
                          goal.FStar_Tactics_Types.context guard
                          goal.FStar_Tactics_Types.opts in
                    bind uu____2228
                      (fun uu____2236  ->
                         let uu____2237 =
                           do_unify goal.FStar_Tactics_Types.context typ
                             goal.FStar_Tactics_Types.goal_ty in
                         if uu____2237
                         then solve goal t1
                         else
                           (let uu____2241 =
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context t1 in
                            let uu____2242 =
                              let uu____2243 =
                                bnorm goal.FStar_Tactics_Types.context typ in
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context uu____2243 in
                            let uu____2244 =
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context
                                goal.FStar_Tactics_Types.goal_ty in
                            fail3
                              "%s : %s does not exactly solve the goal %s"
                              uu____2241 uu____2242 uu____2244))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2253 =
      mlog
        (fun uu____2258  ->
           let uu____2259 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact: tm = %s\n" uu____2259)
        (fun uu____2262  ->
           let uu____2263 = __exact true tm in focus uu____2263) in
    FStar_All.pipe_left (wrap_err "exact") uu____2253
let exact_guard: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2278 =
      mlog
        (fun uu____2283  ->
           let uu____2284 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact_guard: tm = %s\n" uu____2284)
        (fun uu____2287  ->
           let uu____2288 = __exact false tm in focus uu____2288) in
    FStar_All.pipe_left (wrap_err "exact_guard") uu____2278
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2307 =
             let uu____2314 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2314 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2307 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2341 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2361 =
               let uu____2366 = __exact true tm in trytac uu____2366 in
             bind uu____2361
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2379 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2379 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2411  ->
                                let uu____2412 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2412)
                             (fun uu____2415  ->
                                let uu____2416 =
                                  let uu____2417 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2417 in
                                if uu____2416
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2421 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2421
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2441 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2441 in
                                        let uu____2442 =
                                          __apply uopt tm' typ' in
                                        bind uu____2442
                                          (fun uu____2450  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2452 =
                                               let uu____2453 =
                                                 let uu____2456 =
                                                   let uu____2457 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2457 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2456 in
                                               uu____2453.FStar_Syntax_Syntax.n in
                                             match uu____2452 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2485) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2513 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2513
                                                      then ret ()
                                                      else
                                                        (let uu____2517 =
                                                           let uu____2520 =
                                                             let uu___155_2521
                                                               = goal in
                                                             let uu____2522 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2523 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___155_2521.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2522;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2523;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___155_2521.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2520] in
                                                         add_goals uu____2517))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2574 =
        mlog
          (fun uu____2579  ->
             let uu____2580 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2580)
          (fun uu____2582  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2586 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2586
                    (fun uu____2607  ->
                       match uu____2607 with
                       | (tm1,typ,guard) ->
                           let uu____2619 =
                             let uu____2622 =
                               let uu____2625 = __apply uopt tm1 typ in
                               bind uu____2625
                                 (fun uu____2629  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2622 in
                           let uu____2630 =
                             let uu____2633 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context tm1 in
                             let uu____2634 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context typ in
                             let uu____2635 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2633 uu____2634 uu____2635 in
                           try_unif uu____2619 uu____2630))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2574
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2648 =
      let uu____2651 =
        mlog
          (fun uu____2656  ->
             let uu____2657 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2657)
          (fun uu____2660  ->
             let is_unit_t t =
               let uu____2665 =
                 let uu____2666 = FStar_Syntax_Subst.compress t in
                 uu____2666.FStar_Syntax_Syntax.n in
               match uu____2665 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____2670 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____2674 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2674
                    (fun uu____2696  ->
                       match uu____2696 with
                       | (tm1,t,guard) ->
                           let uu____2708 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____2708 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____2738 =
                                     FStar_List.fold_left
                                       (fun uu____2784  ->
                                          fun uu____2785  ->
                                            match (uu____2784, uu____2785)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____2888 =
                                                  is_unit_t b_t in
                                                if uu____2888
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____2926 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____2926 with
                                                   | (u,uu____2956,g_u) ->
                                                       let uu____2970 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____2970,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____2738 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3040 =
                                         let uu____3049 =
                                           let uu____3058 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3058.FStar_Syntax_Syntax.effect_args in
                                         match uu____3049 with
                                         | pre::post::uu____3069 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3110 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3040 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3142 =
                                                let uu____3151 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3151] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3142 in
                                            let uu____3152 =
                                              let uu____3153 =
                                                let uu____3154 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3154
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3153 in
                                            if uu____3152
                                            then
                                              let uu____3157 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3158 =
                                                let uu____3159 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3159 in
                                              let uu____3160 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3157 uu____3158
                                                uu____3160
                                            else
                                              (let solution =
                                                 let uu____3163 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3163 in
                                               let uu____3164 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3164
                                                 (fun uu____3170  ->
                                                    let implicits1 =
                                                      FStar_All.pipe_right
                                                        implicits.FStar_TypeChecker_Env.implicits
                                                        (FStar_List.filter
                                                           (fun uu____3238 
                                                              ->
                                                              match uu____3238
                                                              with
                                                              | (uu____3251,uu____3252,uu____3253,tm2,uu____3255,uu____3256)
                                                                  ->
                                                                  let uu____3257
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    tm2 in
                                                                  (match uu____3257
                                                                   with
                                                                   | 
                                                                   (hd1,uu____3273)
                                                                    ->
                                                                    let uu____3294
                                                                    =
                                                                    let uu____3295
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3295.FStar_Syntax_Syntax.n in
                                                                    (match uu____3294
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3298
                                                                    -> true
                                                                    | 
                                                                    uu____3315
                                                                    -> false)))) in
                                                    let uu____3316 =
                                                      solve goal solution in
                                                    bind uu____3316
                                                      (fun uu____3327  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3338 =
                                                               let uu____3345
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3345 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3338 in
                                                           FStar_List.existsML
                                                             (fun u  ->
                                                                FStar_Syntax_Unionfind.equiv
                                                                  u uv)
                                                             free_uvars in
                                                         let appears uv goals
                                                           =
                                                           FStar_List.existsML
                                                             (fun g'  ->
                                                                is_free_uvar
                                                                  uv
                                                                  g'.FStar_Tactics_Types.goal_ty)
                                                             goals in
                                                         let checkone t1
                                                           goals =
                                                           let uu____3386 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3386
                                                           with
                                                           | (hd1,uu____3402)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3424)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3449
                                                                    -> false) in
                                                         let sub_goals =
                                                           FStar_All.pipe_right
                                                             implicits1
                                                             (FStar_List.map
                                                                (fun
                                                                   uu____3491
                                                                    ->
                                                                   match uu____3491
                                                                   with
                                                                   | 
                                                                   (_msg,_env,_uvar,term,typ,uu____3509)
                                                                    ->
                                                                    let uu___158_3510
                                                                    = goal in
                                                                    let uu____3511
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3512
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___158_3510.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3511;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3512;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___158_3510.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___158_3510.FStar_Tactics_Types.is_guard)
                                                                    })) in
                                                         let rec filter' f xs
                                                           =
                                                           match xs with
                                                           | [] -> []
                                                           | x::xs1 ->
                                                               let uu____3550
                                                                 = f x xs1 in
                                                               if uu____3550
                                                               then
                                                                 let uu____3553
                                                                   =
                                                                   filter' f
                                                                    xs1 in
                                                                 x ::
                                                                   uu____3553
                                                               else
                                                                 filter' f
                                                                   xs1 in
                                                         let sub_goals1 =
                                                           filter'
                                                             (fun g  ->
                                                                fun goals  ->
                                                                  let uu____3567
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                  Prims.op_Negation
                                                                    uu____3567)
                                                             sub_goals in
                                                         let uu____3568 =
                                                           add_goal_from_guard
                                                             "apply_lemma guard"
                                                             goal.FStar_Tactics_Types.context
                                                             guard
                                                             goal.FStar_Tactics_Types.opts in
                                                         bind uu____3568
                                                           (fun uu____3573 
                                                              ->
                                                              let uu____3574
                                                                =
                                                                let uu____3577
                                                                  =
                                                                  let uu____3578
                                                                    =
                                                                    let uu____3579
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____3579 in
                                                                  Prims.op_Negation
                                                                    uu____3578 in
                                                                if uu____3577
                                                                then
                                                                  add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                else ret () in
                                                              bind uu____3574
                                                                (fun
                                                                   uu____3584
                                                                    ->
                                                                   add_goals
                                                                    sub_goals1))))))))))) in
      focus uu____2651 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2648
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3605 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3605 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3615::(e1,uu____3617)::(e2,uu____3619)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3678 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3701 = destruct_eq' typ in
    match uu____3701 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3731 = FStar_Syntax_Util.un_squash typ in
        (match uu____3731 with
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
        let uu____3789 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3789 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3837 = aux e' in
               FStar_Util.map_opt uu____3837
                 (fun uu____3861  ->
                    match uu____3861 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3882 = aux e in
      FStar_Util.map_opt uu____3882
        (fun uu____3906  ->
           match uu____3906 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
let push_bvs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env
  =
  fun e  ->
    fun bvs  ->
      FStar_List.fold_left
        (fun e1  -> fun b  -> FStar_TypeChecker_Env.push_bv e1 b) e bvs
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
          let uu____3967 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____3967
            (fun uu____3991  ->
               match uu____3991 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___159_4008 = bv in
                     let uu____4009 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___159_4008.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___159_4008.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4009
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___160_4018 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___160_4018.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___160_4018.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4032 = h in
         match uu____4032 with
         | (bv,uu____4036) ->
             mlog
               (fun uu____4040  ->
                  let uu____4041 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4042 =
                    FStar_Syntax_Print.term_to_string
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4041
                    uu____4042)
               (fun uu____4045  ->
                  let uu____4046 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4046 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4075 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4075 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4090 =
                             let uu____4091 = FStar_Syntax_Subst.compress x in
                             uu____4091.FStar_Syntax_Syntax.n in
                           (match uu____4090 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___161_4104 = bv1 in
                                  let uu____4105 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___161_4104.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___161_4104.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4105
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4111 =
                                  let uu___162_4112 = goal in
                                  let uu____4113 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4114 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4115 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4113;
                                    FStar_Tactics_Types.witness = uu____4114;
                                    FStar_Tactics_Types.goal_ty = uu____4115;
                                    FStar_Tactics_Types.opts =
                                      (uu___162_4112.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___162_4112.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4111
                            | uu____4116 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4117 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4144 = b in
           match uu____4144 with
           | (bv,uu____4148) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___163_4152 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___163_4152.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___163_4152.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4156 =
                   let uu____4157 =
                     let uu____4164 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4164) in
                   FStar_Syntax_Syntax.NT uu____4157 in
                 [uu____4156] in
               let uu____4165 = subst_goal bv bv' s1 goal in
               (match uu____4165 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4185 = b in
         match uu____4185 with
         | (bv,uu____4189) ->
             let uu____4190 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4190 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4219 = FStar_Syntax_Util.type_u () in
                  (match uu____4219 with
                   | (ty,u) ->
                       let uu____4228 = new_uvar "binder_retype" e0 ty in
                       bind uu____4228
                         (fun t'  ->
                            let bv'' =
                              let uu___164_4238 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___164_4238.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___164_4238.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4242 =
                                let uu____4243 =
                                  let uu____4250 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4250) in
                                FStar_Syntax_Syntax.NT uu____4243 in
                              [uu____4242] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___165_4258 = b1 in
                                   let uu____4259 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___165_4258.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___165_4258.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4259
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4265  ->
                                 let uu____4266 =
                                   let uu____4269 =
                                     let uu____4272 =
                                       let uu___166_4273 = goal in
                                       let uu____4274 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4275 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4274;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4275;
                                         FStar_Tactics_Types.opts =
                                           (uu___166_4273.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___166_4273.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4272] in
                                   add_goals uu____4269 in
                                 bind uu____4266
                                   (fun uu____4278  ->
                                      let uu____4279 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4279
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4302 = b in
           match uu____4302 with
           | (bv,uu____4306) ->
               let uu____4307 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4307 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4339 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4339 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___167_4344 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___167_4344.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___167_4344.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___168_4348 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___168_4348.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___168_4348.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___168_4348.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___168_4348.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4354 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4354 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4376 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4376 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___169_4410 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___169_4410.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___169_4410.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4422 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4422 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4443 = FStar_Syntax_Print.bv_to_string x in
               let uu____4444 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4443 uu____4444
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4451 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4451 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4473 = FStar_Util.set_mem x fns_ty in
           if uu____4473
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4477 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4477
                (fun u  ->
                   let uu____4483 =
                     let uu____4484 = trysolve goal u in
                     Prims.op_Negation uu____4484 in
                   if uu____4483
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___170_4489 = goal in
                        let uu____4490 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4490;
                          FStar_Tactics_Types.goal_ty =
                            (uu___170_4489.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___170_4489.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___170_4489.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4492  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4504 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4504 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4528  ->
                    let uu____4529 = clear b in
                    bind uu____4529
                      (fun uu____4533  ->
                         bind intro (fun uu____4535  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___171_4552 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___171_4552.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___171_4552.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___171_4552.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___171_4552.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4554  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___172_4571 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___172_4571.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___172_4571.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___172_4571.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___172_4571.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4573  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4615 = f x in
          bind uu____4615
            (fun y  ->
               let uu____4623 = mapM f xs in
               bind uu____4623 (fun ys  -> ret (y :: ys)))
let rec tac_fold_env:
  FStar_Tactics_Types.direction ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun d  ->
    fun f  ->
      fun env  ->
        fun t  ->
          let tn =
            let uu____4673 = FStar_Syntax_Subst.compress t in
            uu____4673.FStar_Syntax_Syntax.n in
          let uu____4676 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___174_4682 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___174_4682.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___174_4682.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____4676
            (fun t1  ->
               let tn1 =
                 let uu____4690 =
                   let uu____4691 = FStar_Syntax_Subst.compress t1 in
                   uu____4691.FStar_Syntax_Syntax.n in
                 match uu____4690 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____4723 = ff hd1 in
                     bind uu____4723
                       (fun hd2  ->
                          let fa uu____4743 =
                            match uu____4743 with
                            | (a,q) ->
                                let uu____4756 = ff a in
                                bind uu____4756 (fun a1  -> ret (a1, q)) in
                          let uu____4769 = mapM fa args in
                          bind uu____4769
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____4829 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____4829 with
                      | (bs1,t') ->
                          let uu____4838 =
                            let uu____4841 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____4841 t' in
                          bind uu____4838
                            (fun t''  ->
                               let uu____4845 =
                                 let uu____4846 =
                                   let uu____4863 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____4864 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____4863, uu____4864, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____4846 in
                               ret uu____4845))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____4885 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___173_4892 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___173_4892.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___173_4892.FStar_Syntax_Syntax.vars)
                      } in
                    if d = FStar_Tactics_Types.BottomUp
                    then f env t'
                    else ret t'))
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
            let uu____4926 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4926 with
            | (t1,lcomp,g) ->
                let uu____4938 =
                  (let uu____4941 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____4941) ||
                    (let uu____4943 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4943) in
                if uu____4938
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____4953 = new_uvar "pointwise_rec" env typ in
                     bind uu____4953
                       (fun ut  ->
                          log ps
                            (fun uu____4964  ->
                               let uu____4965 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____4966 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____4965 uu____4966);
                          (let uu____4967 =
                             let uu____4970 =
                               let uu____4971 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____4971 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____4970 opts in
                           bind uu____4967
                             (fun uu____4974  ->
                                let uu____4975 =
                                  bind tau
                                    (fun uu____4981  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____4987  ->
                                            let uu____4988 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____4989 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____4988 uu____4989);
                                       ret ut1) in
                                focus uu____4975))) in
                   let uu____4990 = trytac rewrite_eq in
                   bind uu____4990
                     (fun x  ->
                        match x with
                        | FStar_Pervasives_Native.None  -> ret t1
                        | FStar_Pervasives_Native.Some x1 -> ret x1))
let pointwise:
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____5027 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5027 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5064  ->
                     let uu____5065 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5065);
                bind dismiss_all
                  (fun uu____5068  ->
                     let uu____5069 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5069
                       (fun gt'  ->
                          log ps
                            (fun uu____5079  ->
                               let uu____5080 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5080);
                          (let uu____5081 = push_goals gs in
                           bind uu____5081
                             (fun uu____5085  ->
                                add_goals
                                  [(let uu___175_5087 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___175_5087.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___175_5087.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___175_5087.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___175_5087.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5107 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5107 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5119 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5119 with
            | (hd1,args) ->
                let uu____5152 =
                  let uu____5165 =
                    let uu____5166 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5166.FStar_Syntax_Syntax.n in
                  (uu____5165, args) in
                (match uu____5152 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5180::(l,uu____5182)::(r,uu____5184)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5231 =
                       let uu____5232 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5232 in
                     if uu____5231
                     then
                       let uu____5235 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____5236 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5235 uu____5236
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5239) ->
                     let uu____5256 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5256))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5264 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5264
         (fun u  ->
            let g' =
              let uu___176_5271 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___176_5271.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___176_5271.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___176_5271.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___176_5271.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5274  ->
                 let uu____5275 =
                   let uu____5278 =
                     let uu____5279 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5279
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5278
                     g.FStar_Tactics_Types.opts in
                 bind uu____5275
                   (fun uu____5282  ->
                      let uu____5283 = add_goals [g'] in
                      bind uu____5283 (fun uu____5287  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___177_5304 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___177_5304.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___177_5304.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___177_5304.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___177_5304.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___177_5304.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___177_5304.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___177_5304.FStar_Tactics_Types.psc)
              })
       | uu____5305 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___178_5320 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___178_5320.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___178_5320.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___178_5320.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___178_5320.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___178_5320.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___178_5320.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___178_5320.FStar_Tactics_Types.psc)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5327 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5346 =
      bind cur_goal
        (fun g  ->
           let uu____5360 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5360
             (fun uu____5396  ->
                match uu____5396 with
                | (t1,typ,guard) ->
                    let uu____5412 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5412 with
                     | (hd1,args) ->
                         let uu____5455 =
                           let uu____5468 =
                             let uu____5469 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5469.FStar_Syntax_Syntax.n in
                           (uu____5468, args) in
                         (match uu____5455 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5488)::(q,uu____5490)::[]) when
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
                                let uu___179_5528 = g in
                                let uu____5529 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5529;
                                  FStar_Tactics_Types.witness =
                                    (uu___179_5528.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___179_5528.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___179_5528.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___179_5528.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___180_5531 = g in
                                let uu____5532 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5532;
                                  FStar_Tactics_Types.witness =
                                    (uu___180_5531.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___180_5531.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___180_5531.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___180_5531.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5539  ->
                                   let uu____5540 = add_goals [g1; g2] in
                                   bind uu____5540
                                     (fun uu____5549  ->
                                        let uu____5550 =
                                          let uu____5555 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5556 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5555, uu____5556) in
                                        ret uu____5550))
                          | uu____5561 ->
                              let uu____5574 =
                                FStar_TypeChecker_Normalize.term_to_string
                                  g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5574)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5346
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5613 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5613);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___181_5620 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___181_5620.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___181_5620.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___181_5620.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___181_5620.FStar_Tactics_Types.is_guard)
                 } in
               replace_cur g'
           | FStar_Getopt.Error err1 ->
               fail2 "Setting options `%s` failed: %s" s err1
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
let top_env: FStar_TypeChecker_Env.env tac =
  bind get
    (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
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
      let uu____5658 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____5666 = __tc env tm in
             bind uu____5666
               (fun uu____5686  ->
                  match uu____5686 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____5658
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5719 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5725 =
              let uu____5726 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5726 in
            new_uvar "uvar_env.2" env uu____5725 in
      bind uu____5719
        (fun typ  ->
           let uu____5738 = new_uvar "uvar_env" env typ in
           bind uu____5738 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____5751 =
      bind cur_goal
        (fun goal  ->
           let uu____5757 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____5757
             (fun uu____5777  ->
                match uu____5777 with
                | (t1,typ,guard) ->
                    let uu____5789 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____5789
                      (fun uu____5794  ->
                         let uu____5795 =
                           let uu____5798 =
                             let uu___182_5799 = goal in
                             let uu____5800 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____5801 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___182_5799.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____5800;
                               FStar_Tactics_Types.goal_ty = uu____5801;
                               FStar_Tactics_Types.opts =
                                 (uu___182_5799.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____5798] in
                         add_goals uu____5795))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____5751
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5821 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5821)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5841  ->
             let uu____5842 = FStar_Options.unsafe_tactic_exec () in
             if uu____5842
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5848  -> fun uu____5849  -> false) in
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
      let uu____5871 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5871 with
      | (u,uu____5889,g_u) ->
          let g =
            let uu____5904 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5904;
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
      let uu____5921 = goal_of_goal_ty env typ in
      match uu____5921 with
      | (g,g_u) ->
          let ps =
            {
              FStar_Tactics_Types.main_context = env;
              FStar_Tactics_Types.main_goal = g;
              FStar_Tactics_Types.all_implicits =
                (g_u.FStar_TypeChecker_Env.implicits);
              FStar_Tactics_Types.goals = [g];
              FStar_Tactics_Types.smt_goals = [];
              FStar_Tactics_Types.depth = (Prims.parse_int "0");
              FStar_Tactics_Types.__dump =
                (fun ps  -> fun msg  -> dump_proofstate ps msg);
              FStar_Tactics_Types.psc = FStar_TypeChecker_Normalize.null_psc
            } in
          (ps, (g.FStar_Tactics_Types.witness))