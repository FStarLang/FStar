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
let fail4:
  'Auu____794 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____794 tac
  =
  fun msg  ->
    fun w  ->
      fun x  ->
        fun y  ->
          fun z  ->
            let uu____817 = FStar_Util.format4 msg w x y z in fail uu____817
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____845 = run t ps in
         match uu____845 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success
                ((FStar_Pervasives_Native.Some a), q))
         | FStar_Tactics_Result.Failed (uu____859,uu____860) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let wrap_err: 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____892 = run t ps in
           match uu____892 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____910  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____928 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____942 =
         let uu___135_943 = p in
         let uu____944 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___135_943.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___135_943.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___135_943.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____944;
           FStar_Tactics_Types.smt_goals =
             (uu___135_943.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___135_943.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___135_943.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___135_943.FStar_Tactics_Types.psc)
         } in
       set uu____942)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____959 = trysolve goal solution in
      if uu____959
      then dismiss
      else
        (let uu____963 =
           let uu____964 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____965 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____966 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____964 uu____965
             uu____966 in
         fail uu____963)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___136_973 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___136_973.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___136_973.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___136_973.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___136_973.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___136_973.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___136_973.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___136_973.FStar_Tactics_Types.psc)
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
      let uu____989 = FStar_TypeChecker_Env.pop_bv e in
      match uu____989 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____1007 =
      let uu____1008 = aux b2 env in Prims.op_Negation uu____1008 in
    if uu____1007
    then
      let uu____1009 =
        let uu____1010 = goal_to_string g in
        FStar_Util.format1
          "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
          uu____1010 in
      FStar_Errors.warn
        (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____1009
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___137_1030 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___137_1030.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___137_1030.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___137_1030.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___137_1030.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___137_1030.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___137_1030.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___137_1030.FStar_Tactics_Types.psc)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___138_1049 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___138_1049.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___138_1049.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___138_1049.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___138_1049.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___138_1049.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___138_1049.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___138_1049.FStar_Tactics_Types.psc)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___139_1068 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___139_1068.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___139_1068.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___139_1068.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___139_1068.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___139_1068.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___139_1068.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___139_1068.FStar_Tactics_Types.psc)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___140_1087 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___140_1087.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___140_1087.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___140_1087.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___140_1087.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___140_1087.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___140_1087.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___140_1087.FStar_Tactics_Types.psc)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1097  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___141_1110 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___141_1110.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___141_1110.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___141_1110.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___141_1110.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___141_1110.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___141_1110.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___141_1110.FStar_Tactics_Types.psc)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1139 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1139 with
        | (u,uu____1155,g_u) ->
            let uu____1169 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1169 (fun uu____1173  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1178 = FStar_Syntax_Util.un_squash t in
    match uu____1178 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1188 =
          let uu____1189 = FStar_Syntax_Subst.compress t' in
          uu____1189.FStar_Syntax_Syntax.n in
        (match uu____1188 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1193 -> false)
    | uu____1194 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1203 = FStar_Syntax_Util.un_squash t in
    match uu____1203 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1213 =
          let uu____1214 = FStar_Syntax_Subst.compress t' in
          uu____1214.FStar_Syntax_Syntax.n in
        (match uu____1213 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1218 -> false)
    | uu____1219 -> false
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
          let uu____1257 = new_uvar reason env typ in
          bind uu____1257
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
             let uu____1315 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1315
           with | e1 -> fail "not typeable")
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1354 =
      bind cur_goal
        (fun goal  ->
           let uu____1360 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1360
             (fun uu____1380  ->
                match uu____1380 with
                | (t1,typ,guard) ->
                    let uu____1392 =
                      let uu____1393 =
                        let uu____1394 =
                          FStar_TypeChecker_Rel.discharge_guard
                            goal.FStar_Tactics_Types.context guard in
                        FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                          uu____1394 in
                      Prims.op_Negation uu____1393 in
                    if uu____1392
                    then fail "got non-trivial guard"
                    else ret typ)) in
    FStar_All.pipe_left (wrap_err "tc") uu____1354
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1422 = mk_irrelevant_goal reason env phi opts in
          bind uu____1422 (fun goal  -> add_goals [goal])
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
       let uu____1444 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1444
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1448 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1448))
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
          let uu____1469 =
            let uu____1470 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1470.FStar_TypeChecker_Env.guard_f in
          match uu____1469 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1474 = istrivial e f in
              if uu____1474
              then ret ()
              else
                (let uu____1478 = mk_irrelevant_goal reason e f opts in
                 bind uu____1478
                   (fun goal  ->
                      let goal1 =
                        let uu___144_1485 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___144_1485.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___144_1485.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___144_1485.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___144_1485.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard = true
                        } in
                      push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1491 = is_irrelevant g in
       if uu____1491
       then bind dismiss (fun uu____1495  -> add_smt_goals [g])
       else
         (let uu____1497 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1497))
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
             let uu____1543 =
               try
                 let uu____1577 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1577
               with | uu____1607 -> fail "divide: not enough goals" in
             bind uu____1543
               (fun uu____1634  ->
                  match uu____1634 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___145_1660 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___145_1660.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___145_1660.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___145_1660.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___145_1660.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___145_1660.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___145_1660.FStar_Tactics_Types.psc)
                        } in
                      let rp =
                        let uu___146_1662 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___146_1662.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___146_1662.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___146_1662.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___146_1662.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___146_1662.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___146_1662.FStar_Tactics_Types.psc)
                        } in
                      let uu____1663 = set lp in
                      bind uu____1663
                        (fun uu____1671  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1685 = set rp in
                                     bind uu____1685
                                       (fun uu____1693  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___147_1709 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___147_1709.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___147_1709.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___147_1709.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___147_1709.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___147_1709.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___147_1709.FStar_Tactics_Types.psc)
                                                      } in
                                                    let uu____1710 = set p' in
                                                    bind uu____1710
                                                      (fun uu____1718  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1738 = divide (Prims.parse_int "1") f idtac in
    bind uu____1738
      (fun uu____1751  -> match uu____1751 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1786::uu____1787 ->
             let uu____1790 =
               let uu____1799 = map tau in
               divide (Prims.parse_int "1") tau uu____1799 in
             bind uu____1790
               (fun uu____1817  ->
                  match uu____1817 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1856 =
        bind t1
          (fun uu____1861  ->
             let uu____1862 = map t2 in
             bind uu____1862 (fun uu____1870  -> ret ())) in
      focus uu____1856
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1881 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1881 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1896 =
             let uu____1897 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1897 in
           if uu____1896
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1903 = new_uvar "intro" env' typ' in
              bind uu____1903
                (fun u  ->
                   let uu____1910 =
                     let uu____1911 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1911 in
                   if uu____1910
                   then
                     let uu____1914 =
                       let uu____1917 =
                         let uu___150_1918 = goal in
                         let uu____1919 = bnorm env' u in
                         let uu____1920 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1919;
                           FStar_Tactics_Types.goal_ty = uu____1920;
                           FStar_Tactics_Types.opts =
                             (uu___150_1918.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___150_1918.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1917 in
                     bind uu____1914 (fun uu____1922  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1928 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1928)
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
       (let uu____1949 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1949 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1968 =
              let uu____1969 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1969 in
            if uu____1968
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1985 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1985; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1987 =
                 let uu____1990 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____1990 in
               bind uu____1987
                 (fun u  ->
                    let lb =
                      let uu____2006 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2006 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2010 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2010 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2047 =
                            let uu____2050 =
                              let uu___151_2051 = goal in
                              let uu____2052 = bnorm env' u in
                              let uu____2053 =
                                let uu____2054 = comp_to_typ c in
                                bnorm env' uu____2054 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2052;
                                FStar_Tactics_Types.goal_ty = uu____2053;
                                FStar_Tactics_Types.opts =
                                  (uu___151_2051.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___151_2051.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2050 in
                          bind uu____2047
                            (fun uu____2061  ->
                               let uu____2062 =
                                 let uu____2067 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2067, b) in
                               ret uu____2062)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2081 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2081))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2106 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2106 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___152_2113 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___152_2113.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___152_2113.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___152_2113.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2134 =
          bind get
            (fun ps  ->
               let uu____2140 = __tc e t in
               bind uu____2140
                 (fun uu____2162  ->
                    match uu____2162 with
                    | (t1,uu____2172,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2178 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2178 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2134
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2197 = __tc goal.FStar_Tactics_Types.context t in
         bind uu____2197
           (fun uu____2217  ->
              match uu____2217 with
              | (t1,typ,guard) ->
                  let uu____2229 =
                    let uu____2230 =
                      let uu____2231 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2231 in
                    Prims.op_Negation uu____2230 in
                  if uu____2229
                  then fail "got non-trivial guard"
                  else
                    (let uu____2235 =
                       do_unify goal.FStar_Tactics_Types.context typ
                         goal.FStar_Tactics_Types.goal_ty in
                     if uu____2235
                     then solve goal t1
                     else
                       (let uu____2239 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context t1 in
                        let uu____2240 =
                          let uu____2241 =
                            bnorm goal.FStar_Tactics_Types.context typ in
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context uu____2241 in
                        let uu____2242 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context
                            goal.FStar_Tactics_Types.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2239 uu____2240 uu____2242))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2251 =
      mlog
        (fun uu____2256  ->
           let uu____2257 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact: tm = %s\n" uu____2257)
        (fun uu____2260  -> let uu____2261 = __exact tm in focus uu____2261) in
    FStar_All.pipe_left (wrap_err "exact") uu____2251
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2280 =
             let uu____2287 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2287 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2280 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2314 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2334 =
               let uu____2339 = __exact tm in trytac uu____2339 in
             bind uu____2334
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2352 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2352 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2384  ->
                                let uu____2385 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2385)
                             (fun uu____2388  ->
                                let uu____2389 =
                                  let uu____2390 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2390 in
                                if uu____2389
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2394 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2394
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2414 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2414 in
                                        let uu____2415 =
                                          __apply uopt tm' typ' in
                                        bind uu____2415
                                          (fun uu____2423  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2425 =
                                               let uu____2426 =
                                                 let uu____2429 =
                                                   let uu____2430 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2430 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2429 in
                                               uu____2426.FStar_Syntax_Syntax.n in
                                             match uu____2425 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2458) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2486 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2486
                                                      then ret ()
                                                      else
                                                        (let uu____2490 =
                                                           let uu____2493 =
                                                             let uu___153_2494
                                                               = goal in
                                                             let uu____2495 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2496 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___153_2494.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2495;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2496;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___153_2494.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2493] in
                                                         add_goals uu____2490))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2547 =
        mlog
          (fun uu____2552  ->
             let uu____2553 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2553)
          (fun uu____2555  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2559 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2559
                    (fun uu____2580  ->
                       match uu____2580 with
                       | (tm1,typ,guard) ->
                           let uu____2592 =
                             let uu____2595 =
                               let uu____2598 = __apply uopt tm1 typ in
                               bind uu____2598
                                 (fun uu____2602  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2595 in
                           let uu____2603 =
                             let uu____2606 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context tm1 in
                             let uu____2607 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context typ in
                             let uu____2608 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2606 uu____2607 uu____2608 in
                           try_unif uu____2592 uu____2603))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2547
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2621 =
      let uu____2624 =
        mlog
          (fun uu____2629  ->
             let uu____2630 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2630)
          (fun uu____2633  ->
             let is_unit_t t =
               let uu____2638 =
                 let uu____2639 = FStar_Syntax_Subst.compress t in
                 uu____2639.FStar_Syntax_Syntax.n in
               match uu____2638 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____2643 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____2647 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2647
                    (fun uu____2669  ->
                       match uu____2669 with
                       | (tm1,t,guard) ->
                           let uu____2681 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____2681 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____2711 =
                                     FStar_List.fold_left
                                       (fun uu____2757  ->
                                          fun uu____2758  ->
                                            match (uu____2757, uu____2758)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____2861 =
                                                  is_unit_t b_t in
                                                if uu____2861
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____2899 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____2899 with
                                                   | (u,uu____2929,g_u) ->
                                                       let uu____2943 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____2943,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____2711 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3013 =
                                         let uu____3022 =
                                           let uu____3031 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3031.FStar_Syntax_Syntax.effect_args in
                                         match uu____3022 with
                                         | pre::post::uu____3042 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3083 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3013 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3115 =
                                                let uu____3124 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3124] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3115 in
                                            let ok =
                                              let gopt =
                                                let uu____3129 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                FStar_TypeChecker_Rel.try_teq
                                                  false
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3129
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              match gopt with
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  (FStar_Util.print_string
                                                     "apply_lemma failed outright";
                                                   false)
                                              | FStar_Pervasives_Native.Some
                                                  g ->
                                                  (try
                                                     let g' =
                                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                         goal.FStar_Tactics_Types.context
                                                         g in
                                                     (let uu____3138 =
                                                        FStar_TypeChecker_Rel.guard_to_string
                                                          goal.FStar_Tactics_Types.context
                                                          g' in
                                                      FStar_Util.print1
                                                        "apply_lemma left guard g' = %s\n"
                                                        uu____3138);
                                                     true
                                                   with
                                                   | uu____3143 ->
                                                       ((let uu____3145 =
                                                           FStar_TypeChecker_Rel.guard_to_string
                                                             goal.FStar_Tactics_Types.context
                                                             g in
                                                         FStar_Util.print1
                                                           "apply_lemma failed because of remaining guard g = %s\n"
                                                           uu____3145);
                                                        false)) in
                                            if Prims.op_Negation ok
                                            then
                                              let uu____3148 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3149 =
                                                let uu____3150 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3150 in
                                              let uu____3151 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3148 uu____3149
                                                uu____3151
                                            else
                                              (let solution =
                                                 let uu____3154 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3154 in
                                               let uu____3155 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3155
                                                 (fun uu____3161  ->
                                                    let implicits1 =
                                                      FStar_All.pipe_right
                                                        implicits.FStar_TypeChecker_Env.implicits
                                                        (FStar_List.filter
                                                           (fun uu____3229 
                                                              ->
                                                              match uu____3229
                                                              with
                                                              | (uu____3242,uu____3243,uu____3244,tm2,uu____3246,uu____3247)
                                                                  ->
                                                                  let uu____3248
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    tm2 in
                                                                  (match uu____3248
                                                                   with
                                                                   | 
                                                                   (hd1,uu____3264)
                                                                    ->
                                                                    let uu____3285
                                                                    =
                                                                    let uu____3286
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3286.FStar_Syntax_Syntax.n in
                                                                    (match uu____3285
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3289
                                                                    -> true
                                                                    | 
                                                                    uu____3306
                                                                    -> false)))) in
                                                    let uu____3307 =
                                                      solve goal solution in
                                                    bind uu____3307
                                                      (fun uu____3318  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3329 =
                                                               let uu____3336
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3336 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3329 in
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
                                                           let uu____3377 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3377
                                                           with
                                                           | (hd1,uu____3393)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3415)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3440
                                                                    -> false) in
                                                         let sub_goals =
                                                           FStar_All.pipe_right
                                                             implicits1
                                                             (FStar_List.map
                                                                (fun
                                                                   uu____3482
                                                                    ->
                                                                   match uu____3482
                                                                   with
                                                                   | 
                                                                   (_msg,_env,_uvar,term,typ,uu____3500)
                                                                    ->
                                                                    let uu___158_3501
                                                                    = goal in
                                                                    let uu____3502
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3503
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___158_3501.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3502;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3503;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___158_3501.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___158_3501.FStar_Tactics_Types.is_guard)
                                                                    })) in
                                                         let rec filter' f xs
                                                           =
                                                           match xs with
                                                           | [] -> []
                                                           | x::xs1 ->
                                                               let uu____3541
                                                                 = f x xs1 in
                                                               if uu____3541
                                                               then
                                                                 let uu____3544
                                                                   =
                                                                   filter' f
                                                                    xs1 in
                                                                 x ::
                                                                   uu____3544
                                                               else
                                                                 filter' f
                                                                   xs1 in
                                                         let sub_goals1 =
                                                           filter'
                                                             (fun g  ->
                                                                fun goals  ->
                                                                  let uu____3558
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                  Prims.op_Negation
                                                                    uu____3558)
                                                             sub_goals in
                                                         let uu____3559 =
                                                           add_goal_from_guard
                                                             "apply_lemma guard"
                                                             goal.FStar_Tactics_Types.context
                                                             guard
                                                             goal.FStar_Tactics_Types.opts in
                                                         bind uu____3559
                                                           (fun uu____3564 
                                                              ->
                                                              let uu____3565
                                                                =
                                                                let uu____3568
                                                                  =
                                                                  let uu____3569
                                                                    =
                                                                    let uu____3570
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____3570 in
                                                                  Prims.op_Negation
                                                                    uu____3569 in
                                                                if uu____3568
                                                                then
                                                                  add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                else ret () in
                                                              bind uu____3565
                                                                (fun
                                                                   uu____3575
                                                                    ->
                                                                   add_goals
                                                                    sub_goals1))))))))))) in
      focus uu____2624 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2621
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3596 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3596 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3606::(e1,uu____3608)::(e2,uu____3610)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3669 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3692 = destruct_eq' typ in
    match uu____3692 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3722 = FStar_Syntax_Util.un_squash typ in
        (match uu____3722 with
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
        let uu____3780 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3780 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3828 = aux e' in
               FStar_Util.map_opt uu____3828
                 (fun uu____3852  ->
                    match uu____3852 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3873 = aux e in
      FStar_Util.map_opt uu____3873
        (fun uu____3897  ->
           match uu____3897 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____3958 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____3958
            (fun uu____3982  ->
               match uu____3982 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___159_3999 = bv in
                     let uu____4000 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___159_3999.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___159_3999.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4000
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___160_4009 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___160_4009.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___160_4009.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4023 = h in
         match uu____4023 with
         | (bv,uu____4027) ->
             mlog
               (fun uu____4031  ->
                  let uu____4032 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4033 =
                    FStar_Syntax_Print.term_to_string
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4032
                    uu____4033)
               (fun uu____4036  ->
                  let uu____4037 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4037 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4066 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4066 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4081 =
                             let uu____4082 = FStar_Syntax_Subst.compress x in
                             uu____4082.FStar_Syntax_Syntax.n in
                           (match uu____4081 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___161_4095 = bv1 in
                                  let uu____4096 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___161_4095.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___161_4095.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4096
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4102 =
                                  let uu___162_4103 = goal in
                                  let uu____4104 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4105 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4106 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4104;
                                    FStar_Tactics_Types.witness = uu____4105;
                                    FStar_Tactics_Types.goal_ty = uu____4106;
                                    FStar_Tactics_Types.opts =
                                      (uu___162_4103.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___162_4103.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4102
                            | uu____4107 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4108 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4135 = b in
           match uu____4135 with
           | (bv,uu____4139) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___163_4143 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___163_4143.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___163_4143.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4147 =
                   let uu____4148 =
                     let uu____4155 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4155) in
                   FStar_Syntax_Syntax.NT uu____4148 in
                 [uu____4147] in
               let uu____4156 = subst_goal bv bv' s1 goal in
               (match uu____4156 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4176 = b in
         match uu____4176 with
         | (bv,uu____4180) ->
             let uu____4181 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4181 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4210 = FStar_Syntax_Util.type_u () in
                  (match uu____4210 with
                   | (ty,u) ->
                       let uu____4219 = new_uvar "binder_retype" e0 ty in
                       bind uu____4219
                         (fun t'  ->
                            let bv'' =
                              let uu___164_4229 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___164_4229.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___164_4229.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4233 =
                                let uu____4234 =
                                  let uu____4241 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4241) in
                                FStar_Syntax_Syntax.NT uu____4234 in
                              [uu____4233] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___165_4249 = b1 in
                                   let uu____4250 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___165_4249.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___165_4249.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4250
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4256  ->
                                 let uu____4257 =
                                   let uu____4260 =
                                     let uu____4263 =
                                       let uu___166_4264 = goal in
                                       let uu____4265 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4266 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4265;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4266;
                                         FStar_Tactics_Types.opts =
                                           (uu___166_4264.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___166_4264.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4263] in
                                   add_goals uu____4260 in
                                 bind uu____4257
                                   (fun uu____4269  ->
                                      let uu____4270 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4270
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4293 = b in
           match uu____4293 with
           | (bv,uu____4297) ->
               let uu____4298 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4298 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4330 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4330 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___167_4335 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___167_4335.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___167_4335.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___168_4339 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___168_4339.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___168_4339.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___168_4339.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___168_4339.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4345 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4345 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4367 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4367 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___169_4401 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___169_4401.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___169_4401.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4413 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4413 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4434 = FStar_Syntax_Print.bv_to_string x in
               let uu____4435 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4434 uu____4435
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4442 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4442 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4464 = FStar_Util.set_mem x fns_ty in
           if uu____4464
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4468 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4468
                (fun u  ->
                   let uu____4474 =
                     let uu____4475 = trysolve goal u in
                     Prims.op_Negation uu____4475 in
                   if uu____4474
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___170_4480 = goal in
                        let uu____4481 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4481;
                          FStar_Tactics_Types.goal_ty =
                            (uu___170_4480.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___170_4480.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___170_4480.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4483  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4495 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4495 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4519  ->
                    let uu____4520 = clear b in
                    bind uu____4520
                      (fun uu____4524  ->
                         bind intro (fun uu____4526  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___171_4543 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___171_4543.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___171_4543.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___171_4543.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___171_4543.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4545  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___172_4562 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___172_4562.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___172_4562.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___172_4562.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___172_4562.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4564  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4606 = f x in
          bind uu____4606
            (fun y  ->
               let uu____4614 = mapM f xs in
               bind uu____4614 (fun ys  -> ret (y :: ys)))
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
            let uu____4664 = FStar_Syntax_Subst.compress t in
            uu____4664.FStar_Syntax_Syntax.n in
          let uu____4667 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___174_4673 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___174_4673.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___174_4673.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____4667
            (fun t1  ->
               let tn1 =
                 match tn with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____4710 = ff hd1 in
                     bind uu____4710
                       (fun hd2  ->
                          let fa uu____4730 =
                            match uu____4730 with
                            | (a,q) ->
                                let uu____4743 = ff a in
                                bind uu____4743 (fun a1  -> ret (a1, q)) in
                          let uu____4756 = mapM fa args in
                          bind uu____4756
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____4816 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____4816 with
                      | (bs1,t') ->
                          let uu____4825 =
                            let uu____4828 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____4828 t' in
                          bind uu____4825
                            (fun t''  ->
                               let uu____4832 =
                                 let uu____4833 =
                                   let uu____4850 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____4851 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____4850, uu____4851, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____4833 in
                               ret uu____4832))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____4872 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___173_4879 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___173_4879.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___173_4879.FStar_Syntax_Syntax.vars)
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
            let uu____4913 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4913 with
            | (t1,lcomp,g) ->
                let uu____4925 =
                  (let uu____4928 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____4928) ||
                    (let uu____4930 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4930) in
                if uu____4925
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____4940 = new_uvar "pointwise_rec" env typ in
                     bind uu____4940
                       (fun ut  ->
                          log ps
                            (fun uu____4951  ->
                               let uu____4952 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____4953 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____4952 uu____4953);
                          (let uu____4954 =
                             let uu____4957 =
                               let uu____4958 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____4958 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____4957 opts in
                           bind uu____4954
                             (fun uu____4961  ->
                                let uu____4962 =
                                  bind tau
                                    (fun uu____4967  ->
                                       log ps
                                         (fun uu____4973  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut in
                                            let uu____4975 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____4976 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____4975 uu____4976);
                                       ret ut) in
                                focus uu____4962))) in
                   let uu____4977 = trytac rewrite_eq in
                   bind uu____4977
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
           let uu____5014 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5014 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5051  ->
                     let uu____5052 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5052);
                bind dismiss_all
                  (fun uu____5055  ->
                     let uu____5056 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5056
                       (fun gt'  ->
                          log ps
                            (fun uu____5066  ->
                               let uu____5067 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5067);
                          (let uu____5068 = push_goals gs in
                           bind uu____5068
                             (fun uu____5072  ->
                                add_goals
                                  [(let uu___175_5074 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___175_5074.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___175_5074.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___175_5074.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___175_5074.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5094 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5094 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5106 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5106 with
            | (hd1,args) ->
                let uu____5139 =
                  let uu____5152 =
                    let uu____5153 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5153.FStar_Syntax_Syntax.n in
                  (uu____5152, args) in
                (match uu____5139 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5167::(l,uu____5169)::(r,uu____5171)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5218 =
                       let uu____5219 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5219 in
                     if uu____5218
                     then
                       let uu____5222 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____5223 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5222 uu____5223
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5226) ->
                     let uu____5243 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5243))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5251 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5251
         (fun u  ->
            let g' =
              let uu___176_5258 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___176_5258.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___176_5258.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___176_5258.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___176_5258.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5261  ->
                 let uu____5262 =
                   let uu____5265 =
                     let uu____5266 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5266
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5265
                     g.FStar_Tactics_Types.opts in
                 bind uu____5262
                   (fun uu____5269  ->
                      let uu____5270 = add_goals [g'] in
                      bind uu____5270 (fun uu____5274  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___177_5291 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___177_5291.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___177_5291.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___177_5291.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___177_5291.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___177_5291.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___177_5291.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___177_5291.FStar_Tactics_Types.psc)
              })
       | uu____5292 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___178_5307 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___178_5307.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___178_5307.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___178_5307.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___178_5307.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___178_5307.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___178_5307.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___178_5307.FStar_Tactics_Types.psc)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5314 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5333 =
      bind cur_goal
        (fun g  ->
           let uu____5347 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5347
             (fun uu____5383  ->
                match uu____5383 with
                | (t1,typ,guard) ->
                    let uu____5399 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5399 with
                     | (hd1,args) ->
                         let uu____5442 =
                           let uu____5455 =
                             let uu____5456 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5456.FStar_Syntax_Syntax.n in
                           (uu____5455, args) in
                         (match uu____5442 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5475)::(q,uu____5477)::[]) when
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
                                let uu___179_5515 = g in
                                let uu____5516 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5516;
                                  FStar_Tactics_Types.witness =
                                    (uu___179_5515.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___179_5515.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___179_5515.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___179_5515.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___180_5518 = g in
                                let uu____5519 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5519;
                                  FStar_Tactics_Types.witness =
                                    (uu___180_5518.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___180_5518.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___180_5518.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___180_5518.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5526  ->
                                   let uu____5527 = add_goals [g1; g2] in
                                   bind uu____5527
                                     (fun uu____5536  ->
                                        let uu____5537 =
                                          let uu____5542 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5543 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5542, uu____5543) in
                                        ret uu____5537))
                          | uu____5548 ->
                              let uu____5561 =
                                FStar_TypeChecker_Normalize.term_to_string
                                  g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5561)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5333
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5600 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5600);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___181_5607 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___181_5607.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___181_5607.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___181_5607.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___181_5607.FStar_Tactics_Types.is_guard)
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
      let uu____5645 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____5653 = __tc env tm in
             bind uu____5653
               (fun uu____5673  ->
                  match uu____5673 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____5645
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5706 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5712 =
              let uu____5713 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5713 in
            new_uvar "uvar_env.2" env uu____5712 in
      bind uu____5706
        (fun typ  ->
           let uu____5725 = new_uvar "uvar_env" env typ in
           bind uu____5725 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____5738 =
      bind cur_goal
        (fun goal  ->
           let uu____5744 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____5744
             (fun uu____5764  ->
                match uu____5764 with
                | (t1,typ,guard) ->
                    let uu____5776 =
                      let uu____5777 =
                        let uu____5778 =
                          FStar_TypeChecker_Rel.discharge_guard
                            goal.FStar_Tactics_Types.context guard in
                        FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                          uu____5778 in
                      Prims.op_Negation uu____5777 in
                    if uu____5776
                    then fail "got non-trivial guard"
                    else
                      (let uu____5782 =
                         let uu____5785 =
                           let uu___182_5786 = goal in
                           let uu____5787 =
                             bnorm goal.FStar_Tactics_Types.context t1 in
                           let uu____5788 =
                             bnorm goal.FStar_Tactics_Types.context typ in
                           {
                             FStar_Tactics_Types.context =
                               (uu___182_5786.FStar_Tactics_Types.context);
                             FStar_Tactics_Types.witness = uu____5787;
                             FStar_Tactics_Types.goal_ty = uu____5788;
                             FStar_Tactics_Types.opts =
                               (uu___182_5786.FStar_Tactics_Types.opts);
                             FStar_Tactics_Types.is_guard = false
                           } in
                         [uu____5785] in
                       add_goals uu____5782))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____5738
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5808 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5808)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5828  ->
             let uu____5829 = FStar_Options.unsafe_tactic_exec () in
             if uu____5829
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5835  -> fun uu____5836  -> false) in
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
      let uu____5858 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5858 with
      | (u,uu____5876,g_u) ->
          let g =
            let uu____5891 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5891;
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
      let uu____5908 = goal_of_goal_ty env typ in
      match uu____5908 with
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