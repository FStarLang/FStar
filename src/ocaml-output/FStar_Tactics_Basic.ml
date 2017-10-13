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
let print_proof_state1:
  FStar_TypeChecker_Normalize.psc -> Prims.string -> Prims.unit tac =
  fun psc  ->
    fun msg  ->
      mk_tac
        (fun ps  ->
           let subst1 = FStar_TypeChecker_Normalize.psc_subst psc in
           let ps1 = FStar_Tactics_Types.subst_proof_state subst1 ps in
           dump_cur ps1 msg; FStar_Tactics_Result.Success ((), ps1))
let print_proof_state:
  FStar_TypeChecker_Normalize.psc -> Prims.string -> Prims.unit tac =
  fun psc  ->
    fun msg  ->
      mk_tac
        (fun ps  ->
           let subst1 = FStar_TypeChecker_Normalize.psc_subst psc in
           let ps1 = FStar_Tactics_Types.subst_proof_state subst1 ps in
           dump_proofstate ps1 msg; FStar_Tactics_Result.Success ((), ps1))
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
          ((let uu____610 =
              let uu____613 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____613 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____610);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'Auu____703 . Prims.string -> 'Auu____703 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____714 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____714
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____722 . Prims.string -> Prims.string -> 'Auu____722 tac =
  fun msg  ->
    fun x  -> let uu____733 = FStar_Util.format1 msg x in fail uu____733
let fail2:
  'Auu____742 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____742 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____757 = FStar_Util.format2 msg x y in fail uu____757
let fail3:
  'Auu____768 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____768 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____787 = FStar_Util.format3 msg x y z in fail uu____787
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____815 = run t ps in
         match uu____815 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success
                ((FStar_Pervasives_Native.Some a), q))
         | FStar_Tactics_Result.Failed (uu____829,uu____830) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____845  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____863 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____877 =
         let uu___119_878 = p in
         let uu____879 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___119_878.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___119_878.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___119_878.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____879;
           FStar_Tactics_Types.smt_goals =
             (uu___119_878.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___119_878.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___119_878.FStar_Tactics_Types.__dump)
         } in
       set uu____877)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____894 = trysolve goal solution in
      if uu____894
      then dismiss
      else
        (let uu____898 =
           let uu____899 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____900 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____901 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____899 uu____900
             uu____901 in
         fail uu____898)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___120_908 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___120_908.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___120_908.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___120_908.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___120_908.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___120_908.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___120_908.FStar_Tactics_Types.__dump)
          }))
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___121_925 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___121_925.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___121_925.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___121_925.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___121_925.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___121_925.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___121_925.FStar_Tactics_Types.__dump)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___122_942 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___122_942.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___122_942.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___122_942.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___122_942.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___122_942.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___122_942.FStar_Tactics_Types.__dump)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___123_959 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___123_959.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___123_959.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___123_959.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___123_959.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___123_959.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___123_959.FStar_Tactics_Types.__dump)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___124_976 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___124_976.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___124_976.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___124_976.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___124_976.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___124_976.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___124_976.FStar_Tactics_Types.__dump)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____986  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___125_999 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___125_999.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___125_999.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___125_999.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___125_999.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___125_999.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___125_999.FStar_Tactics_Types.__dump)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1028 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1028 with
        | (u,uu____1044,g_u) ->
            let uu____1058 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1058 (fun uu____1062  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1067 = FStar_Syntax_Util.un_squash t in
    match uu____1067 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1077 =
          let uu____1078 = FStar_Syntax_Subst.compress t' in
          uu____1078.FStar_Syntax_Syntax.n in
        (match uu____1077 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1082 -> false)
    | uu____1083 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1092 = FStar_Syntax_Util.un_squash t in
    match uu____1092 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1102 =
          let uu____1103 = FStar_Syntax_Subst.compress t' in
          uu____1103.FStar_Syntax_Syntax.n in
        (match uu____1102 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1107 -> false)
    | uu____1108 -> false
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
          let uu____1146 = new_uvar reason env typ in
          bind uu____1146
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
             let uu____1204 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1204
           with | e1 -> fail "not typeable")
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1246 = __tc goal.FStar_Tactics_Types.context t in
         bind uu____1246
           (fun uu____1266  ->
              match uu____1266 with
              | (t1,typ,guard) ->
                  let uu____1278 =
                    let uu____1279 =
                      let uu____1280 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1280 in
                    Prims.op_Negation uu____1279 in
                  if uu____1278
                  then fail "tc: got non-trivial guard"
                  else ret typ))
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1304 = mk_irrelevant_goal reason env phi opts in
          bind uu____1304 (fun goal  -> add_goals [goal])
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
       let uu____1326 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1326
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1330 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1330))
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
          let uu____1351 =
            let uu____1352 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1352.FStar_TypeChecker_Env.guard_f in
          match uu____1351 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1356 = istrivial e f in
              if uu____1356
              then ret ()
              else
                (let uu____1360 = mk_irrelevant_goal reason e f opts in
                 bind uu____1360
                   (fun goal  ->
                      let goal1 =
                        let uu___128_1367 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___128_1367.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___128_1367.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___128_1367.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___128_1367.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard = true
                        } in
                      push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1373 = is_irrelevant g in
       if uu____1373
       then bind dismiss (fun uu____1377  -> add_smt_goals [g])
       else
         (let uu____1379 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1379))
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
             let uu____1425 =
               try
                 let uu____1459 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1459
               with | uu____1489 -> fail "divide: not enough goals" in
             bind uu____1425
               (fun uu____1516  ->
                  match uu____1516 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___129_1542 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___129_1542.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___129_1542.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___129_1542.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___129_1542.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___129_1542.FStar_Tactics_Types.__dump)
                        } in
                      let rp =
                        let uu___130_1544 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___130_1544.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___130_1544.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___130_1544.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___130_1544.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___130_1544.FStar_Tactics_Types.__dump)
                        } in
                      let uu____1545 = set lp in
                      bind uu____1545
                        (fun uu____1553  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1567 = set rp in
                                     bind uu____1567
                                       (fun uu____1575  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___131_1591 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___131_1591.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___131_1591.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___131_1591.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___131_1591.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___131_1591.FStar_Tactics_Types.__dump)
                                                      } in
                                                    let uu____1592 = set p' in
                                                    bind uu____1592
                                                      (fun uu____1600  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1620 = divide (Prims.parse_int "1") f idtac in
    bind uu____1620
      (fun uu____1633  -> match uu____1633 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1668::uu____1669 ->
             let uu____1672 =
               let uu____1681 = map tau in
               divide (Prims.parse_int "1") tau uu____1681 in
             bind uu____1672
               (fun uu____1699  ->
                  match uu____1699 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1738 =
        bind t1
          (fun uu____1743  ->
             let uu____1744 = map t2 in
             bind uu____1744 (fun uu____1752  -> ret ())) in
      focus uu____1738
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1763 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1763 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1778 =
             let uu____1779 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1779 in
           if uu____1778
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1785 = new_uvar "intro" env' typ' in
              bind uu____1785
                (fun u  ->
                   let uu____1792 =
                     let uu____1793 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1793 in
                   if uu____1792
                   then
                     let uu____1796 =
                       let uu____1799 =
                         let uu___134_1800 = goal in
                         let uu____1801 = bnorm env' u in
                         let uu____1802 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1801;
                           FStar_Tactics_Types.goal_ty = uu____1802;
                           FStar_Tactics_Types.opts =
                             (uu___134_1800.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___134_1800.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1799 in
                     bind uu____1796 (fun uu____1804  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1810 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1810)
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
       (let uu____1831 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1831 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1850 =
              let uu____1851 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1851 in
            if uu____1850
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1867 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1867; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1869 =
                 let uu____1872 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____1872 in
               bind uu____1869
                 (fun u  ->
                    let lb =
                      let uu____1888 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____1888 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1892 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1892 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____1929 =
                            let uu____1932 =
                              let uu___135_1933 = goal in
                              let uu____1934 = bnorm env' u in
                              let uu____1935 =
                                let uu____1936 = comp_to_typ c in
                                bnorm env' uu____1936 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____1934;
                                FStar_Tactics_Types.goal_ty = uu____1935;
                                FStar_Tactics_Types.opts =
                                  (uu___135_1933.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___135_1933.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____1932 in
                          bind uu____1929
                            (fun uu____1943  ->
                               let uu____1944 =
                                 let uu____1949 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____1949, b) in
                               ret uu____1944)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____1963 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1963))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____1988 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1988 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___136_1995 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___136_1995.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___136_1995.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___136_1995.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        bind get
          (fun ps  ->
             let uu____2019 = __tc e t in
             bind uu____2019
               (fun uu____2041  ->
                  match uu____2041 with
                  | (t1,uu____2051,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                       (let steps =
                          let uu____2057 =
                            FStar_TypeChecker_Normalize.tr_norm_steps s in
                          FStar_List.append
                            [FStar_TypeChecker_Normalize.Reify;
                            FStar_TypeChecker_Normalize.UnfoldTac] uu____2057 in
                        let t2 =
                          normalize steps ps.FStar_Tactics_Types.main_context
                            t1 in
                        ret t2))))
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2072 = __tc goal.FStar_Tactics_Types.context t in
         bind uu____2072
           (fun uu____2092  ->
              match uu____2092 with
              | (t1,typ,guard) ->
                  let uu____2104 =
                    let uu____2105 =
                      let uu____2106 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2106 in
                    Prims.op_Negation uu____2105 in
                  if uu____2104
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2110 =
                       do_unify goal.FStar_Tactics_Types.context typ
                         goal.FStar_Tactics_Types.goal_ty in
                     if uu____2110
                     then solve goal t1
                     else
                       (let uu____2114 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context t1 in
                        let uu____2115 =
                          let uu____2116 =
                            bnorm goal.FStar_Tactics_Types.context typ in
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context uu____2116 in
                        let uu____2117 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context
                            goal.FStar_Tactics_Types.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2114 uu____2115 uu____2117))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    mlog
      (fun uu____2128  ->
         let uu____2129 = FStar_Syntax_Print.term_to_string tm in
         FStar_Util.print1 "exact: tm = %s\n" uu____2129)
      (fun uu____2132  -> let uu____2133 = __exact tm in focus uu____2133)
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2148 =
             let uu____2155 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2155 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2148 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2182 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2202 =
               let uu____2207 = __exact tm in trytac uu____2207 in
             bind uu____2202
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2220 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2220 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2252  ->
                                let uu____2253 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2253)
                             (fun uu____2256  ->
                                let uu____2257 =
                                  let uu____2258 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2258 in
                                if uu____2257
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2262 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2262
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2282 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2282 in
                                        let uu____2283 =
                                          __apply uopt tm' typ' in
                                        bind uu____2283
                                          (fun uu____2291  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2293 =
                                               let uu____2294 =
                                                 let uu____2297 =
                                                   let uu____2298 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2298 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2297 in
                                               uu____2294.FStar_Syntax_Syntax.n in
                                             match uu____2293 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2326) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2354 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2354
                                                      then ret ()
                                                      else
                                                        (let uu____2358 =
                                                           let uu____2361 =
                                                             let uu___137_2362
                                                               = goal in
                                                             let uu____2363 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2364 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___137_2362.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2363;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2364;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___137_2362.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2361] in
                                                         add_goals uu____2358))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      mlog
        (fun uu____2417  ->
           let uu____2418 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "apply: tm = %s\n" uu____2418)
        (fun uu____2420  ->
           bind cur_goal
             (fun goal  ->
                let uu____2424 = __tc goal.FStar_Tactics_Types.context tm in
                bind uu____2424
                  (fun uu____2445  ->
                     match uu____2445 with
                     | (tm1,typ,guard) ->
                         let uu____2457 =
                           let uu____2460 =
                             let uu____2463 = __apply uopt tm1 typ in
                             bind uu____2463
                               (fun uu____2467  ->
                                  add_goal_from_guard "apply guard"
                                    goal.FStar_Tactics_Types.context guard
                                    goal.FStar_Tactics_Types.opts) in
                           focus uu____2460 in
                         let uu____2468 =
                           let uu____2471 =
                             FStar_TypeChecker_Normalize.term_to_string
                               goal.FStar_Tactics_Types.context tm1 in
                           let uu____2472 =
                             FStar_TypeChecker_Normalize.term_to_string
                               goal.FStar_Tactics_Types.context typ in
                           let uu____2473 =
                             FStar_TypeChecker_Normalize.term_to_string
                               goal.FStar_Tactics_Types.context
                               goal.FStar_Tactics_Types.goal_ty in
                           fail3
                             "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                             uu____2471 uu____2472 uu____2473 in
                         try_unif uu____2457 uu____2468)))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2482 =
      mlog
        (fun uu____2487  ->
           let uu____2488 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2488)
        (fun uu____2491  ->
           let is_unit_t t =
             let uu____2496 =
               let uu____2497 = FStar_Syntax_Subst.compress t in
               uu____2497.FStar_Syntax_Syntax.n in
             match uu____2496 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid
                 -> true
             | uu____2501 -> false in
           bind cur_goal
             (fun goal  ->
                let uu____2505 = __tc goal.FStar_Tactics_Types.context tm in
                bind uu____2505
                  (fun uu____2527  ->
                     match uu____2527 with
                     | (tm1,t,guard) ->
                         let uu____2539 =
                           FStar_Syntax_Util.arrow_formals_comp t in
                         (match uu____2539 with
                          | (bs,comp) ->
                              if
                                Prims.op_Negation
                                  (FStar_Syntax_Util.is_lemma_comp comp)
                              then fail "apply_lemma: not a lemma"
                              else
                                (let uu____2569 =
                                   FStar_List.fold_left
                                     (fun uu____2615  ->
                                        fun uu____2616  ->
                                          match (uu____2615, uu____2616) with
                                          | ((uvs,guard1,subst1),(b,aq)) ->
                                              let b_t =
                                                FStar_Syntax_Subst.subst
                                                  subst1
                                                  b.FStar_Syntax_Syntax.sort in
                                              let uu____2719 = is_unit_t b_t in
                                              if uu____2719
                                              then
                                                (((FStar_Syntax_Util.exp_unit,
                                                    aq) :: uvs), guard1,
                                                  ((FStar_Syntax_Syntax.NT
                                                      (b,
                                                        FStar_Syntax_Util.exp_unit))
                                                  :: subst1))
                                              else
                                                (let uu____2757 =
                                                   FStar_TypeChecker_Util.new_implicit_var
                                                     "apply_lemma"
                                                     (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                     goal.FStar_Tactics_Types.context
                                                     b_t in
                                                 match uu____2757 with
                                                 | (u,uu____2787,g_u) ->
                                                     let uu____2801 =
                                                       FStar_TypeChecker_Rel.conj_guard
                                                         guard1 g_u in
                                                     (((u, aq) :: uvs),
                                                       uu____2801,
                                                       ((FStar_Syntax_Syntax.NT
                                                           (b, u)) ::
                                                       subst1))))
                                     ([], guard, []) bs in
                                 match uu____2569 with
                                 | (uvs,implicits,subst1) ->
                                     let uvs1 = FStar_List.rev uvs in
                                     let comp1 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp in
                                     let uu____2871 =
                                       let uu____2880 =
                                         let uu____2889 =
                                           FStar_Syntax_Util.comp_to_comp_typ
                                             comp1 in
                                         uu____2889.FStar_Syntax_Syntax.effect_args in
                                       match uu____2880 with
                                       | pre::post::uu____2900 ->
                                           ((FStar_Pervasives_Native.fst pre),
                                             (FStar_Pervasives_Native.fst
                                                post))
                                       | uu____2941 ->
                                           failwith
                                             "apply_lemma: impossible: not a lemma" in
                                     (match uu____2871 with
                                      | (pre,post) ->
                                          let uu____2970 =
                                            let uu____2971 =
                                              let uu____2972 =
                                                FStar_Syntax_Util.mk_squash
                                                  post in
                                              do_unify
                                                goal.FStar_Tactics_Types.context
                                                uu____2972
                                                goal.FStar_Tactics_Types.goal_ty in
                                            Prims.op_Negation uu____2971 in
                                          if uu____2970
                                          then
                                            let uu____2975 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                goal.FStar_Tactics_Types.context
                                                tm1 in
                                            let uu____2976 =
                                              let uu____2977 =
                                                FStar_Syntax_Util.mk_squash
                                                  post in
                                              FStar_TypeChecker_Normalize.term_to_string
                                                goal.FStar_Tactics_Types.context
                                                uu____2977 in
                                            let uu____2978 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                goal.FStar_Tactics_Types.context
                                                goal.FStar_Tactics_Types.goal_ty in
                                            fail3
                                              "apply_lemma: Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                              uu____2975 uu____2976
                                              uu____2978
                                          else
                                            (let solution =
                                               let uu____2981 =
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   tm1 uvs1
                                                   FStar_Pervasives_Native.None
                                                   (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                               FStar_TypeChecker_Normalize.normalize
                                                 [FStar_TypeChecker_Normalize.Beta]
                                                 goal.FStar_Tactics_Types.context
                                                 uu____2981 in
                                             let uu____2982 =
                                               add_implicits
                                                 implicits.FStar_TypeChecker_Env.implicits in
                                             bind uu____2982
                                               (fun uu____2988  ->
                                                  let implicits1 =
                                                    FStar_All.pipe_right
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                      (FStar_List.filter
                                                         (fun uu____3056  ->
                                                            match uu____3056
                                                            with
                                                            | (uu____3069,uu____3070,uu____3071,tm2,uu____3073,uu____3074)
                                                                ->
                                                                let uu____3075
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    tm2 in
                                                                (match uu____3075
                                                                 with
                                                                 | (hd1,uu____3091)
                                                                    ->
                                                                    let uu____3112
                                                                    =
                                                                    let uu____3113
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3113.FStar_Syntax_Syntax.n in
                                                                    (match uu____3112
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3116
                                                                    -> true
                                                                    | 
                                                                    uu____3133
                                                                    -> false)))) in
                                                  let uu____3134 =
                                                    solve goal solution in
                                                  bind uu____3134
                                                    (fun uu____3145  ->
                                                       let is_free_uvar uv t1
                                                         =
                                                         let free_uvars =
                                                           let uu____3156 =
                                                             let uu____3163 =
                                                               FStar_Syntax_Free.uvars
                                                                 t1 in
                                                             FStar_Util.set_elements
                                                               uu____3163 in
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.fst
                                                             uu____3156 in
                                                         FStar_List.existsML
                                                           (fun u  ->
                                                              FStar_Syntax_Unionfind.equiv
                                                                u uv)
                                                           free_uvars in
                                                       let appears uv goals =
                                                         FStar_List.existsML
                                                           (fun g'  ->
                                                              is_free_uvar uv
                                                                g'.FStar_Tactics_Types.goal_ty)
                                                           goals in
                                                       let checkone t1 goals
                                                         =
                                                         let uu____3204 =
                                                           FStar_Syntax_Util.head_and_args
                                                             t1 in
                                                         match uu____3204
                                                         with
                                                         | (hd1,uu____3220)
                                                             ->
                                                             (match hd1.FStar_Syntax_Syntax.n
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_uvar
                                                                  (uv,uu____3242)
                                                                  ->
                                                                  appears uv
                                                                    goals
                                                              | uu____3267 ->
                                                                  false) in
                                                       let sub_goals =
                                                         FStar_All.pipe_right
                                                           implicits1
                                                           (FStar_List.map
                                                              (fun uu____3309
                                                                  ->
                                                                 match uu____3309
                                                                 with
                                                                 | (_msg,_env,_uvar,term,typ,uu____3327)
                                                                    ->
                                                                    let uu___140_3328
                                                                    = goal in
                                                                    let uu____3329
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3330
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___140_3328.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3329;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3330;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___140_3328.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___140_3328.FStar_Tactics_Types.is_guard)
                                                                    })) in
                                                       let rec filter' f xs =
                                                         match xs with
                                                         | [] -> []
                                                         | x::xs1 ->
                                                             let uu____3368 =
                                                               f x xs1 in
                                                             if uu____3368
                                                             then
                                                               let uu____3371
                                                                 =
                                                                 filter' f
                                                                   xs1 in
                                                               x ::
                                                                 uu____3371
                                                             else
                                                               filter' f xs1 in
                                                       let sub_goals1 =
                                                         filter'
                                                           (fun g  ->
                                                              fun goals  ->
                                                                let uu____3385
                                                                  =
                                                                  checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                Prims.op_Negation
                                                                  uu____3385)
                                                           sub_goals in
                                                       let uu____3386 =
                                                         add_goal_from_guard
                                                           "apply_lemma guard"
                                                           goal.FStar_Tactics_Types.context
                                                           guard
                                                           goal.FStar_Tactics_Types.opts in
                                                       bind uu____3386
                                                         (fun uu____3391  ->
                                                            let uu____3392 =
                                                              let uu____3395
                                                                =
                                                                let uu____3396
                                                                  =
                                                                  let uu____3397
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                  istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____3397 in
                                                                Prims.op_Negation
                                                                  uu____3396 in
                                                              if uu____3395
                                                              then
                                                                add_irrelevant_goal
                                                                  "apply_lemma precondition"
                                                                  goal.FStar_Tactics_Types.context
                                                                  pre
                                                                  goal.FStar_Tactics_Types.opts
                                                              else ret () in
                                                            bind uu____3392
                                                              (fun uu____3402
                                                                  ->
                                                                 add_goals
                                                                   sub_goals1))))))))))) in
    focus uu____2482
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3419 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3419 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3429::(e1,uu____3431)::(e2,uu____3433)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3492 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3515 = destruct_eq' typ in
    match uu____3515 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3545 = FStar_Syntax_Util.un_squash typ in
        (match uu____3545 with
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
        let uu____3603 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3603 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3651 = aux e' in
               FStar_Util.map_opt uu____3651
                 (fun uu____3675  ->
                    match uu____3675 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3696 = aux e in
      FStar_Util.map_opt uu____3696
        (fun uu____3720  ->
           match uu____3720 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____3781 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____3781
            (fun uu____3805  ->
               match uu____3805 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___141_3822 = bv in
                     let uu____3823 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___141_3822.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___141_3822.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3823
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___142_3832 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___142_3832.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___142_3832.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3846 = h in
         match uu____3846 with
         | (bv,uu____3850) ->
             mlog
               (fun uu____3854  ->
                  let uu____3855 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____3856 =
                    FStar_Syntax_Print.term_to_string
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3855
                    uu____3856)
               (fun uu____3859  ->
                  let uu____3860 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____3860 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____3889 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____3889 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____3904 =
                             let uu____3905 = FStar_Syntax_Subst.compress x in
                             uu____3905.FStar_Syntax_Syntax.n in
                           (match uu____3904 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___143_3918 = bv1 in
                                  let uu____3919 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___143_3918.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___143_3918.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____3919
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____3925 =
                                  let uu___144_3926 = goal in
                                  let uu____3927 = push_bvs e0 (bv :: bvs1) in
                                  let uu____3928 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____3929 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____3927;
                                    FStar_Tactics_Types.witness = uu____3928;
                                    FStar_Tactics_Types.goal_ty = uu____3929;
                                    FStar_Tactics_Types.opts =
                                      (uu___144_3926.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___144_3926.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____3925
                            | uu____3930 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____3931 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3958 = b in
           match uu____3958 with
           | (bv,uu____3962) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___145_3966 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___145_3966.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___145_3966.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3970 =
                   let uu____3971 =
                     let uu____3978 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3978) in
                   FStar_Syntax_Syntax.NT uu____3971 in
                 [uu____3970] in
               let uu____3979 = subst_goal bv bv' s1 goal in
               (match uu____3979 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____3999 = b in
         match uu____3999 with
         | (bv,uu____4003) ->
             let uu____4004 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4004 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4033 = FStar_Syntax_Util.type_u () in
                  (match uu____4033 with
                   | (ty,u) ->
                       let uu____4042 = new_uvar "binder_retype" e0 ty in
                       bind uu____4042
                         (fun t'  ->
                            let bv'' =
                              let uu___146_4052 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___146_4052.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___146_4052.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4056 =
                                let uu____4057 =
                                  let uu____4064 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4064) in
                                FStar_Syntax_Syntax.NT uu____4057 in
                              [uu____4056] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___147_4072 = b1 in
                                   let uu____4073 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___147_4072.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___147_4072.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4073
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4079  ->
                                 let uu____4080 =
                                   let uu____4083 =
                                     let uu____4086 =
                                       let uu___148_4087 = goal in
                                       let uu____4088 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4089 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4088;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4089;
                                         FStar_Tactics_Types.opts =
                                           (uu___148_4087.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___148_4087.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4086] in
                                   add_goals uu____4083 in
                                 bind uu____4080
                                   (fun uu____4092  ->
                                      let uu____4093 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4093
                                        goal.FStar_Tactics_Types.opts))))))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4099 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4099 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4121 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4121 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___149_4155 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___149_4155.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___149_4155.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4167 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4167 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4188 = FStar_Syntax_Print.bv_to_string x in
               let uu____4189 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4188 uu____4189
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4196 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4196 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4218 = FStar_Util.set_mem x fns_ty in
           if uu____4218
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4222 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4222
                (fun u  ->
                   let uu____4228 =
                     let uu____4229 = trysolve goal u in
                     Prims.op_Negation uu____4229 in
                   if uu____4228
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___150_4234 = goal in
                        let uu____4235 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4235;
                          FStar_Tactics_Types.goal_ty =
                            (uu___150_4234.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___150_4234.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___150_4234.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4237  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4249 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4249 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4273  ->
                    let uu____4274 = clear b in
                    bind uu____4274
                      (fun uu____4278  ->
                         bind intro (fun uu____4280  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___151_4297 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___151_4297.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___151_4297.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___151_4297.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___151_4297.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4299  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___152_4316 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___152_4316.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___152_4316.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___152_4316.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___152_4316.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4318  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4360 = f x in
          bind uu____4360
            (fun y  ->
               let uu____4368 = mapM f xs in
               bind uu____4368 (fun ys  -> ret (y :: ys)))
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
            let uu____4418 = FStar_Syntax_Subst.compress t in
            uu____4418.FStar_Syntax_Syntax.n in
          let uu____4421 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___154_4427 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___154_4427.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___154_4427.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____4421
            (fun t1  ->
               let tn1 =
                 match tn with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____4464 = ff hd1 in
                     bind uu____4464
                       (fun hd2  ->
                          let fa uu____4484 =
                            match uu____4484 with
                            | (a,q) ->
                                let uu____4497 = ff a in
                                bind uu____4497 (fun a1  -> ret (a1, q)) in
                          let uu____4510 = mapM fa args in
                          bind uu____4510
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____4570 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____4570 with
                      | (bs1,t') ->
                          let uu____4579 =
                            let uu____4582 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____4582 t' in
                          bind uu____4579
                            (fun t''  ->
                               let uu____4586 =
                                 let uu____4587 =
                                   let uu____4604 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____4605 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____4604, uu____4605, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____4587 in
                               ret uu____4586))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____4626 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___153_4633 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___153_4633.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___153_4633.FStar_Syntax_Syntax.vars)
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
            let uu____4667 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4667 with
            | (t1,lcomp,g) ->
                let uu____4679 =
                  (let uu____4682 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____4682) ||
                    (let uu____4684 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4684) in
                if uu____4679
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4691 = new_uvar "pointwise_rec" env typ in
                   bind uu____4691
                     (fun ut  ->
                        log ps
                          (fun uu____4702  ->
                             let uu____4703 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4704 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4703 uu____4704);
                        (let uu____4705 =
                           let uu____4708 =
                             let uu____4709 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4709 typ t1 ut in
                           add_irrelevant_goal "pointwise_rec equation" env
                             uu____4708 opts in
                         bind uu____4705
                           (fun uu____4712  ->
                              let uu____4713 =
                                bind tau
                                  (fun uu____4718  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4713))))
let pointwise:
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____4743 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____4743 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____4780  ->
                     let uu____4781 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____4781);
                bind dismiss_all
                  (fun uu____4784  ->
                     let uu____4785 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____4785
                       (fun gt'  ->
                          log ps
                            (fun uu____4795  ->
                               let uu____4796 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____4796);
                          (let uu____4797 = push_goals gs in
                           bind uu____4797
                             (fun uu____4801  ->
                                add_goals
                                  [(let uu___155_4803 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___155_4803.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___155_4803.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___155_4803.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___155_4803.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4823 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____4823 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4835 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4835 with
            | (hd1,args) ->
                let uu____4868 =
                  let uu____4881 =
                    let uu____4882 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4882.FStar_Syntax_Syntax.n in
                  (uu____4881, args) in
                (match uu____4868 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4896::(l,uu____4898)::(r,uu____4900)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4947 =
                       let uu____4948 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____4948 in
                     if uu____4947
                     then
                       let uu____4951 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____4952 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4951 uu____4952
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____4955) ->
                     let uu____4972 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____4972))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4980 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____4980
         (fun u  ->
            let g' =
              let uu___156_4987 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___156_4987.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___156_4987.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___156_4987.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___156_4987.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____4990  ->
                 let uu____4991 =
                   let uu____4994 =
                     let uu____4995 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4995
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____4994
                     g.FStar_Tactics_Types.opts in
                 bind uu____4991
                   (fun uu____4998  ->
                      let uu____4999 = add_goals [g'] in
                      bind uu____4999 (fun uu____5003  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___157_5020 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___157_5020.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___157_5020.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___157_5020.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___157_5020.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___157_5020.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___157_5020.FStar_Tactics_Types.__dump)
              })
       | uu____5021 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___158_5036 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___158_5036.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___158_5036.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___158_5036.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___158_5036.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___158_5036.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___158_5036.FStar_Tactics_Types.__dump)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5043 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____5069 = __tc g.FStar_Tactics_Types.context t in
         bind uu____5069
           (fun uu____5105  ->
              match uu____5105 with
              | (t1,typ,guard) ->
                  let uu____5121 = FStar_Syntax_Util.head_and_args typ in
                  (match uu____5121 with
                   | (hd1,args) ->
                       let uu____5164 =
                         let uu____5177 =
                           let uu____5178 = FStar_Syntax_Util.un_uinst hd1 in
                           uu____5178.FStar_Syntax_Syntax.n in
                         (uu____5177, args) in
                       (match uu____5164 with
                        | (FStar_Syntax_Syntax.Tm_fvar
                           fv,(p,uu____5197)::(q,uu____5199)::[]) when
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
                              let uu___159_5237 = g in
                              let uu____5238 =
                                FStar_TypeChecker_Env.push_bv
                                  g.FStar_Tactics_Types.context v_p in
                              {
                                FStar_Tactics_Types.context = uu____5238;
                                FStar_Tactics_Types.witness =
                                  (uu___159_5237.FStar_Tactics_Types.witness);
                                FStar_Tactics_Types.goal_ty =
                                  (uu___159_5237.FStar_Tactics_Types.goal_ty);
                                FStar_Tactics_Types.opts =
                                  (uu___159_5237.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___159_5237.FStar_Tactics_Types.is_guard)
                              } in
                            let g2 =
                              let uu___160_5240 = g in
                              let uu____5241 =
                                FStar_TypeChecker_Env.push_bv
                                  g.FStar_Tactics_Types.context v_q in
                              {
                                FStar_Tactics_Types.context = uu____5241;
                                FStar_Tactics_Types.witness =
                                  (uu___160_5240.FStar_Tactics_Types.witness);
                                FStar_Tactics_Types.goal_ty =
                                  (uu___160_5240.FStar_Tactics_Types.goal_ty);
                                FStar_Tactics_Types.opts =
                                  (uu___160_5240.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___160_5240.FStar_Tactics_Types.is_guard)
                              } in
                            bind dismiss
                              (fun uu____5248  ->
                                 let uu____5249 = add_goals [g1; g2] in
                                 bind uu____5249
                                   (fun uu____5258  ->
                                      let uu____5259 =
                                        let uu____5264 =
                                          FStar_Syntax_Syntax.bv_to_name v_p in
                                        let uu____5265 =
                                          FStar_Syntax_Syntax.bv_to_name v_q in
                                        (uu____5264, uu____5265) in
                                      ret uu____5259))
                        | uu____5270 ->
                            let uu____5283 =
                              FStar_TypeChecker_Normalize.term_to_string
                                g.FStar_Tactics_Types.context typ in
                            fail1 "Not a disjunction: %s" uu____5283))))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5306 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5306);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___161_5313 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___161_5313.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___161_5313.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___161_5313.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___161_5313.FStar_Tactics_Types.is_guard)
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
      bind cur_goal
        (fun goal  ->
           let env =
             FStar_TypeChecker_Env.set_expected_typ
               goal.FStar_Tactics_Types.context ty in
           let uu____5356 = __tc env tm in
           bind uu____5356
             (fun uu____5376  ->
                match uu____5376 with
                | (tm1,typ,guard) ->
                    (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                     ret tm1)))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5405 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5411 =
              let uu____5412 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5412 in
            new_uvar "uvar_env.2" env uu____5411 in
      bind uu____5405
        (fun typ  ->
           let uu____5424 = new_uvar "uvar_env" env typ in
           bind uu____5424 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____5440 = __tc goal.FStar_Tactics_Types.context t in
         bind uu____5440
           (fun uu____5460  ->
              match uu____5460 with
              | (t1,typ,guard) ->
                  let uu____5472 =
                    let uu____5473 =
                      let uu____5474 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____5474 in
                    Prims.op_Negation uu____5473 in
                  if uu____5472
                  then fail "unshelve: got non-trivial guard"
                  else
                    (let uu____5478 =
                       let uu____5481 =
                         let uu___162_5482 = goal in
                         let uu____5483 =
                           bnorm goal.FStar_Tactics_Types.context t1 in
                         let uu____5484 =
                           bnorm goal.FStar_Tactics_Types.context typ in
                         {
                           FStar_Tactics_Types.context =
                             (uu___162_5482.FStar_Tactics_Types.context);
                           FStar_Tactics_Types.witness = uu____5483;
                           FStar_Tactics_Types.goal_ty = uu____5484;
                           FStar_Tactics_Types.opts =
                             (uu___162_5482.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard = false
                         } in
                       [uu____5481] in
                     add_goals uu____5478)))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5500 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5500)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5520  ->
             let uu____5521 = FStar_Options.unsafe_tactic_exec () in
             if uu____5521
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5527  -> fun uu____5528  -> false) in
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
      let uu____5550 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5550 with
      | (u,uu____5568,g_u) ->
          let g =
            let uu____5583 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5583;
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
      let uu____5600 = goal_of_goal_ty env typ in
      match uu____5600 with
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
                (fun ps  -> fun msg  -> dump_proofstate ps msg)
            } in
          (ps, (g.FStar_Tactics_Types.witness))