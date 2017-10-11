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
      let uu____540 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____540 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____594 =
              let uu____597 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____597 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____594);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'Auu____687 . Prims.string -> 'Auu____687 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____698 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____698
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____706 . Prims.string -> Prims.string -> 'Auu____706 tac =
  fun msg  ->
    fun x  -> let uu____717 = FStar_Util.format1 msg x in fail uu____717
let fail2:
  'Auu____726 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____726 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____741 = FStar_Util.format2 msg x y in fail uu____741
let fail3:
  'Auu____752 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____752 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____771 = FStar_Util.format3 msg x y z in fail uu____771
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____799 = run t ps in
         match uu____799 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success
                ((FStar_Pervasives_Native.Some a), q))
         | FStar_Tactics_Result.Failed (uu____813,uu____814) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____829  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____847 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____861 =
         let uu___117_862 = p in
         let uu____863 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___117_862.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___117_862.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___117_862.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____863;
           FStar_Tactics_Types.smt_goals =
             (uu___117_862.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___117_862.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___117_862.FStar_Tactics_Types.__dump)
         } in
       set uu____861)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____878 = trysolve goal solution in
      if uu____878
      then dismiss
      else
        (let uu____882 =
           let uu____883 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____884 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____885 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____883 uu____884
             uu____885 in
         fail uu____882)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___118_892 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___118_892.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___118_892.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___118_892.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___118_892.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___118_892.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___118_892.FStar_Tactics_Types.__dump)
          }))
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___119_909 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___119_909.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___119_909.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___119_909.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___119_909.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___119_909.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___119_909.FStar_Tactics_Types.__dump)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___120_926 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___120_926.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___120_926.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___120_926.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___120_926.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___120_926.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___120_926.FStar_Tactics_Types.__dump)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___121_943 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___121_943.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___121_943.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___121_943.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___121_943.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___121_943.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___121_943.FStar_Tactics_Types.__dump)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___122_960 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___122_960.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___122_960.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___122_960.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___122_960.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___122_960.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___122_960.FStar_Tactics_Types.__dump)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____970  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___123_983 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___123_983.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___123_983.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___123_983.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___123_983.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___123_983.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___123_983.FStar_Tactics_Types.__dump)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1012 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1012 with
        | (u,uu____1028,g_u) ->
            let uu____1042 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1042 (fun uu____1046  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1051 = FStar_Syntax_Util.un_squash t in
    match uu____1051 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1061 =
          let uu____1062 = FStar_Syntax_Subst.compress t' in
          uu____1062.FStar_Syntax_Syntax.n in
        (match uu____1061 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1066 -> false)
    | uu____1067 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1076 = FStar_Syntax_Util.un_squash t in
    match uu____1076 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1086 =
          let uu____1087 = FStar_Syntax_Subst.compress t' in
          uu____1087.FStar_Syntax_Syntax.n in
        (match uu____1086 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1091 -> false)
    | uu____1092 -> false
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
          let uu____1130 = new_uvar reason env typ in
          bind uu____1130
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
             let uu____1188 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1188
           with | e1 -> fail "not typeable")
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1230 = __tc goal.FStar_Tactics_Types.context t in
         bind uu____1230
           (fun uu____1250  ->
              match uu____1250 with
              | (t1,typ,guard) ->
                  let uu____1262 =
                    let uu____1263 =
                      let uu____1264 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1264 in
                    Prims.op_Negation uu____1263 in
                  if uu____1262
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
          let uu____1288 = mk_irrelevant_goal reason env phi opts in
          bind uu____1288 (fun goal  -> add_goals [goal])
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
       let uu____1310 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1310
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1314 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1314))
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
          let uu____1335 =
            let uu____1336 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1336.FStar_TypeChecker_Env.guard_f in
          match uu____1335 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1340 = istrivial e f in
              if uu____1340
              then ret ()
              else
                (let uu____1344 = mk_irrelevant_goal reason e f opts in
                 bind uu____1344
                   (fun goal  ->
                      let goal1 =
                        let uu___126_1351 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___126_1351.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___126_1351.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___126_1351.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___126_1351.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard = true
                        } in
                      push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1357 = is_irrelevant g in
       if uu____1357
       then bind dismiss (fun uu____1361  -> add_smt_goals [g])
       else
         (let uu____1363 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1363))
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
             let uu____1409 =
               try
                 let uu____1443 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1443
               with | uu____1473 -> fail "divide: not enough goals" in
             bind uu____1409
               (fun uu____1500  ->
                  match uu____1500 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___127_1526 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___127_1526.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___127_1526.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___127_1526.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___127_1526.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___127_1526.FStar_Tactics_Types.__dump)
                        } in
                      let rp =
                        let uu___128_1528 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___128_1528.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___128_1528.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___128_1528.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___128_1528.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___128_1528.FStar_Tactics_Types.__dump)
                        } in
                      let uu____1529 = set lp in
                      bind uu____1529
                        (fun uu____1537  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1551 = set rp in
                                     bind uu____1551
                                       (fun uu____1559  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___129_1575 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___129_1575.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___129_1575.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___129_1575.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___129_1575.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___129_1575.FStar_Tactics_Types.__dump)
                                                      } in
                                                    let uu____1576 = set p' in
                                                    bind uu____1576
                                                      (fun uu____1584  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1604 = divide (Prims.parse_int "1") f idtac in
    bind uu____1604
      (fun uu____1617  -> match uu____1617 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1652::uu____1653 ->
             let uu____1656 =
               let uu____1665 = map tau in
               divide (Prims.parse_int "1") tau uu____1665 in
             bind uu____1656
               (fun uu____1683  ->
                  match uu____1683 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1722 =
        bind t1
          (fun uu____1727  ->
             let uu____1728 = map t2 in
             bind uu____1728 (fun uu____1736  -> ret ())) in
      focus uu____1722
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1747 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1747 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1762 =
             let uu____1763 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1763 in
           if uu____1762
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1769 = new_uvar "intro" env' typ' in
              bind uu____1769
                (fun u  ->
                   let uu____1776 =
                     let uu____1777 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1777 in
                   if uu____1776
                   then
                     let uu____1780 =
                       let uu____1783 =
                         let uu___132_1784 = goal in
                         let uu____1785 = bnorm env' u in
                         let uu____1786 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1785;
                           FStar_Tactics_Types.goal_ty = uu____1786;
                           FStar_Tactics_Types.opts =
                             (uu___132_1784.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___132_1784.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1783 in
                     bind uu____1780 (fun uu____1788  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1794 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1794)
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
       (let uu____1815 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1815 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1834 =
              let uu____1835 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1835 in
            if uu____1834
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1851 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1851; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1853 =
                 let uu____1856 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____1856 in
               bind uu____1853
                 (fun u  ->
                    let lb =
                      let uu____1872 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____1872 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1876 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1876 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____1913 =
                            let uu____1916 =
                              let uu___133_1917 = goal in
                              let uu____1918 = bnorm env' u in
                              let uu____1919 =
                                let uu____1920 = comp_to_typ c in
                                bnorm env' uu____1920 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____1918;
                                FStar_Tactics_Types.goal_ty = uu____1919;
                                FStar_Tactics_Types.opts =
                                  (uu___133_1917.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___133_1917.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____1916 in
                          bind uu____1913
                            (fun uu____1927  ->
                               let uu____1928 =
                                 let uu____1933 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____1933, b) in
                               ret uu____1928)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____1947 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1947))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____1972 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1972 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___134_1979 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___134_1979.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___134_1979.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___134_1979.FStar_Tactics_Types.is_guard)
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
             let uu____2003 = __tc e t in
             bind uu____2003
               (fun uu____2025  ->
                  match uu____2025 with
                  | (t1,uu____2035,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                       (let steps =
                          let uu____2041 =
                            FStar_TypeChecker_Normalize.tr_norm_steps s in
                          FStar_List.append
                            [FStar_TypeChecker_Normalize.Reify;
                            FStar_TypeChecker_Normalize.UnfoldTac] uu____2041 in
                        let t2 =
                          normalize steps ps.FStar_Tactics_Types.main_context
                            t1 in
                        ret t2))))
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2056 = __tc goal.FStar_Tactics_Types.context t in
         bind uu____2056
           (fun uu____2076  ->
              match uu____2076 with
              | (t1,typ,guard) ->
                  let uu____2088 =
                    let uu____2089 =
                      let uu____2090 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2090 in
                    Prims.op_Negation uu____2089 in
                  if uu____2088
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2094 =
                       do_unify goal.FStar_Tactics_Types.context typ
                         goal.FStar_Tactics_Types.goal_ty in
                     if uu____2094
                     then solve goal t1
                     else
                       (let uu____2098 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context t1 in
                        let uu____2099 =
                          let uu____2100 =
                            bnorm goal.FStar_Tactics_Types.context typ in
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context uu____2100 in
                        let uu____2101 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context
                            goal.FStar_Tactics_Types.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2098 uu____2099 uu____2101))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    mlog
      (fun uu____2112  ->
         let uu____2113 = FStar_Syntax_Print.term_to_string tm in
         FStar_Util.print1 "exact: tm = %s\n" uu____2113)
      (fun uu____2116  -> let uu____2117 = __exact tm in focus uu____2117)
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2132 =
             let uu____2139 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2139 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2132 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2166 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2186 =
               let uu____2191 = __exact tm in trytac uu____2191 in
             bind uu____2186
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2204 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2204 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2236  ->
                                let uu____2237 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2237)
                             (fun uu____2240  ->
                                let uu____2241 =
                                  let uu____2242 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2242 in
                                if uu____2241
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2246 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2246
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2266 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2266 in
                                        let uu____2267 =
                                          __apply uopt tm' typ' in
                                        bind uu____2267
                                          (fun uu____2275  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2277 =
                                               let uu____2278 =
                                                 let uu____2281 =
                                                   let uu____2282 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2282 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2281 in
                                               uu____2278.FStar_Syntax_Syntax.n in
                                             match uu____2277 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2310) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2338 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2338
                                                      then ret ()
                                                      else
                                                        (let uu____2342 =
                                                           let uu____2345 =
                                                             let uu___135_2346
                                                               = goal in
                                                             let uu____2347 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2348 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___135_2346.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2347;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2348;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___135_2346.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2345] in
                                                         add_goals uu____2342))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      mlog
        (fun uu____2401  ->
           let uu____2402 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "apply: tm = %s\n" uu____2402)
        (fun uu____2404  ->
           bind cur_goal
             (fun goal  ->
                let uu____2408 = __tc goal.FStar_Tactics_Types.context tm in
                bind uu____2408
                  (fun uu____2429  ->
                     match uu____2429 with
                     | (tm1,typ,guard) ->
                         let uu____2441 =
                           let uu____2444 =
                             let uu____2447 = __apply uopt tm1 typ in
                             bind uu____2447
                               (fun uu____2451  ->
                                  add_goal_from_guard "apply guard"
                                    goal.FStar_Tactics_Types.context guard
                                    goal.FStar_Tactics_Types.opts) in
                           focus uu____2444 in
                         let uu____2452 =
                           let uu____2455 =
                             FStar_TypeChecker_Normalize.term_to_string
                               goal.FStar_Tactics_Types.context tm1 in
                           let uu____2456 =
                             FStar_TypeChecker_Normalize.term_to_string
                               goal.FStar_Tactics_Types.context typ in
                           let uu____2457 =
                             FStar_TypeChecker_Normalize.term_to_string
                               goal.FStar_Tactics_Types.context
                               goal.FStar_Tactics_Types.goal_ty in
                           fail3
                             "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                             uu____2455 uu____2456 uu____2457 in
                         try_unif uu____2441 uu____2452)))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2466 =
      mlog
        (fun uu____2471  ->
           let uu____2472 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2472)
        (fun uu____2475  ->
           let is_unit_t t =
             let uu____2480 =
               let uu____2481 = FStar_Syntax_Subst.compress t in
               uu____2481.FStar_Syntax_Syntax.n in
             match uu____2480 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid
                 -> true
             | uu____2485 -> false in
           bind cur_goal
             (fun goal  ->
                let uu____2489 = __tc goal.FStar_Tactics_Types.context tm in
                bind uu____2489
                  (fun uu____2511  ->
                     match uu____2511 with
                     | (tm1,t,guard) ->
                         let uu____2523 =
                           FStar_Syntax_Util.arrow_formals_comp t in
                         (match uu____2523 with
                          | (bs,comp) ->
                              if
                                Prims.op_Negation
                                  (FStar_Syntax_Util.is_lemma_comp comp)
                              then fail "apply_lemma: not a lemma"
                              else
                                (let uu____2553 =
                                   FStar_List.fold_left
                                     (fun uu____2599  ->
                                        fun uu____2600  ->
                                          match (uu____2599, uu____2600) with
                                          | ((uvs,guard1,subst1),(b,aq)) ->
                                              let b_t =
                                                FStar_Syntax_Subst.subst
                                                  subst1
                                                  b.FStar_Syntax_Syntax.sort in
                                              let uu____2703 = is_unit_t b_t in
                                              if uu____2703
                                              then
                                                (((FStar_Syntax_Util.exp_unit,
                                                    aq) :: uvs), guard1,
                                                  ((FStar_Syntax_Syntax.NT
                                                      (b,
                                                        FStar_Syntax_Util.exp_unit))
                                                  :: subst1))
                                              else
                                                (let uu____2741 =
                                                   FStar_TypeChecker_Util.new_implicit_var
                                                     "apply_lemma"
                                                     (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                     goal.FStar_Tactics_Types.context
                                                     b_t in
                                                 match uu____2741 with
                                                 | (u,uu____2771,g_u) ->
                                                     let uu____2785 =
                                                       FStar_TypeChecker_Rel.conj_guard
                                                         guard1 g_u in
                                                     (((u, aq) :: uvs),
                                                       uu____2785,
                                                       ((FStar_Syntax_Syntax.NT
                                                           (b, u)) ::
                                                       subst1))))
                                     ([], guard, []) bs in
                                 match uu____2553 with
                                 | (uvs,implicits,subst1) ->
                                     let uvs1 = FStar_List.rev uvs in
                                     let comp1 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp in
                                     let uu____2855 =
                                       let uu____2864 =
                                         let uu____2873 =
                                           FStar_Syntax_Util.comp_to_comp_typ
                                             comp1 in
                                         uu____2873.FStar_Syntax_Syntax.effect_args in
                                       match uu____2864 with
                                       | pre::post::uu____2884 ->
                                           ((FStar_Pervasives_Native.fst pre),
                                             (FStar_Pervasives_Native.fst
                                                post))
                                       | uu____2925 ->
                                           failwith
                                             "apply_lemma: impossible: not a lemma" in
                                     (match uu____2855 with
                                      | (pre,post) ->
                                          let uu____2954 =
                                            let uu____2955 =
                                              let uu____2956 =
                                                FStar_Syntax_Util.mk_squash
                                                  post in
                                              do_unify
                                                goal.FStar_Tactics_Types.context
                                                uu____2956
                                                goal.FStar_Tactics_Types.goal_ty in
                                            Prims.op_Negation uu____2955 in
                                          if uu____2954
                                          then
                                            let uu____2959 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                goal.FStar_Tactics_Types.context
                                                tm1 in
                                            let uu____2960 =
                                              let uu____2961 =
                                                FStar_Syntax_Util.mk_squash
                                                  post in
                                              FStar_TypeChecker_Normalize.term_to_string
                                                goal.FStar_Tactics_Types.context
                                                uu____2961 in
                                            let uu____2962 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                goal.FStar_Tactics_Types.context
                                                goal.FStar_Tactics_Types.goal_ty in
                                            fail3
                                              "apply_lemma: Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                              uu____2959 uu____2960
                                              uu____2962
                                          else
                                            (let solution =
                                               let uu____2965 =
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   tm1 uvs1
                                                   FStar_Pervasives_Native.None
                                                   (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                               FStar_TypeChecker_Normalize.normalize
                                                 [FStar_TypeChecker_Normalize.Beta]
                                                 goal.FStar_Tactics_Types.context
                                                 uu____2965 in
                                             let uu____2966 =
                                               add_implicits
                                                 implicits.FStar_TypeChecker_Env.implicits in
                                             bind uu____2966
                                               (fun uu____2972  ->
                                                  let implicits1 =
                                                    FStar_All.pipe_right
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                      (FStar_List.filter
                                                         (fun uu____3040  ->
                                                            match uu____3040
                                                            with
                                                            | (uu____3053,uu____3054,uu____3055,tm2,uu____3057,uu____3058)
                                                                ->
                                                                let uu____3059
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    tm2 in
                                                                (match uu____3059
                                                                 with
                                                                 | (hd1,uu____3075)
                                                                    ->
                                                                    let uu____3096
                                                                    =
                                                                    let uu____3097
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3097.FStar_Syntax_Syntax.n in
                                                                    (match uu____3096
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3100
                                                                    -> true
                                                                    | 
                                                                    uu____3117
                                                                    -> false)))) in
                                                  let uu____3118 =
                                                    solve goal solution in
                                                  bind uu____3118
                                                    (fun uu____3129  ->
                                                       let is_free_uvar uv t1
                                                         =
                                                         let free_uvars =
                                                           let uu____3140 =
                                                             let uu____3147 =
                                                               FStar_Syntax_Free.uvars
                                                                 t1 in
                                                             FStar_Util.set_elements
                                                               uu____3147 in
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.fst
                                                             uu____3140 in
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
                                                         let uu____3188 =
                                                           FStar_Syntax_Util.head_and_args
                                                             t1 in
                                                         match uu____3188
                                                         with
                                                         | (hd1,uu____3204)
                                                             ->
                                                             (match hd1.FStar_Syntax_Syntax.n
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_uvar
                                                                  (uv,uu____3226)
                                                                  ->
                                                                  appears uv
                                                                    goals
                                                              | uu____3251 ->
                                                                  false) in
                                                       let sub_goals =
                                                         FStar_All.pipe_right
                                                           implicits1
                                                           (FStar_List.map
                                                              (fun uu____3293
                                                                  ->
                                                                 match uu____3293
                                                                 with
                                                                 | (_msg,_env,_uvar,term,typ,uu____3311)
                                                                    ->
                                                                    let uu___138_3312
                                                                    = goal in
                                                                    let uu____3313
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3314
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___138_3312.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3313;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3314;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___138_3312.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___138_3312.FStar_Tactics_Types.is_guard)
                                                                    })) in
                                                       let rec filter' f xs =
                                                         match xs with
                                                         | [] -> []
                                                         | x::xs1 ->
                                                             let uu____3352 =
                                                               f x xs1 in
                                                             if uu____3352
                                                             then
                                                               let uu____3355
                                                                 =
                                                                 filter' f
                                                                   xs1 in
                                                               x ::
                                                                 uu____3355
                                                             else
                                                               filter' f xs1 in
                                                       let sub_goals1 =
                                                         filter'
                                                           (fun g  ->
                                                              fun goals  ->
                                                                let uu____3369
                                                                  =
                                                                  checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                Prims.op_Negation
                                                                  uu____3369)
                                                           sub_goals in
                                                       let uu____3370 =
                                                         add_goal_from_guard
                                                           "apply_lemma guard"
                                                           goal.FStar_Tactics_Types.context
                                                           guard
                                                           goal.FStar_Tactics_Types.opts in
                                                       bind uu____3370
                                                         (fun uu____3375  ->
                                                            let uu____3376 =
                                                              let uu____3379
                                                                =
                                                                let uu____3380
                                                                  =
                                                                  let uu____3381
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                  istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____3381 in
                                                                Prims.op_Negation
                                                                  uu____3380 in
                                                              if uu____3379
                                                              then
                                                                add_irrelevant_goal
                                                                  "apply_lemma precondition"
                                                                  goal.FStar_Tactics_Types.context
                                                                  pre
                                                                  goal.FStar_Tactics_Types.opts
                                                              else ret () in
                                                            bind uu____3376
                                                              (fun uu____3386
                                                                  ->
                                                                 add_goals
                                                                   sub_goals1))))))))))) in
    focus uu____2466
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3403 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3403 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3413::(e1,uu____3415)::(e2,uu____3417)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3476 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3499 = destruct_eq' typ in
    match uu____3499 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3529 = FStar_Syntax_Util.un_squash typ in
        (match uu____3529 with
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
        let uu____3587 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3587 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3635 = aux e' in
               FStar_Util.map_opt uu____3635
                 (fun uu____3659  ->
                    match uu____3659 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3680 = aux e in
      FStar_Util.map_opt uu____3680
        (fun uu____3704  ->
           match uu____3704 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____3765 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____3765
            (fun uu____3789  ->
               match uu____3789 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___139_3806 = bv in
                     let uu____3807 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___139_3806.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___139_3806.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3807
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___140_3816 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___140_3816.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___140_3816.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3830 = h in
         match uu____3830 with
         | (bv,uu____3834) ->
             mlog
               (fun uu____3838  ->
                  let uu____3839 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____3840 =
                    FStar_Syntax_Print.term_to_string
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3839
                    uu____3840)
               (fun uu____3843  ->
                  let uu____3844 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____3844 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____3873 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____3873 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____3888 =
                             let uu____3889 = FStar_Syntax_Subst.compress x in
                             uu____3889.FStar_Syntax_Syntax.n in
                           (match uu____3888 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___141_3902 = bv1 in
                                  let uu____3903 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___141_3902.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___141_3902.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____3903
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____3909 =
                                  let uu___142_3910 = goal in
                                  let uu____3911 = push_bvs e0 (bv :: bvs1) in
                                  let uu____3912 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____3913 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____3911;
                                    FStar_Tactics_Types.witness = uu____3912;
                                    FStar_Tactics_Types.goal_ty = uu____3913;
                                    FStar_Tactics_Types.opts =
                                      (uu___142_3910.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___142_3910.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____3909
                            | uu____3914 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____3915 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3942 = b in
           match uu____3942 with
           | (bv,uu____3946) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___143_3950 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___143_3950.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___143_3950.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3954 =
                   let uu____3955 =
                     let uu____3962 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3962) in
                   FStar_Syntax_Syntax.NT uu____3955 in
                 [uu____3954] in
               let uu____3963 = subst_goal bv bv' s1 goal in
               (match uu____3963 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____3983 = b in
         match uu____3983 with
         | (bv,uu____3987) ->
             let uu____3988 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____3988 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4017 = FStar_Syntax_Util.type_u () in
                  (match uu____4017 with
                   | (ty,u) ->
                       let uu____4026 = new_uvar "binder_retype" e0 ty in
                       bind uu____4026
                         (fun t'  ->
                            let bv'' =
                              let uu___144_4036 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___144_4036.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___144_4036.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4040 =
                                let uu____4041 =
                                  let uu____4048 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4048) in
                                FStar_Syntax_Syntax.NT uu____4041 in
                              [uu____4040] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___145_4056 = b1 in
                                   let uu____4057 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___145_4056.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___145_4056.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4057
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4063  ->
                                 let uu____4064 =
                                   let uu____4067 =
                                     let uu____4070 =
                                       let uu___146_4071 = goal in
                                       let uu____4072 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4073 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4072;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4073;
                                         FStar_Tactics_Types.opts =
                                           (uu___146_4071.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___146_4071.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4070] in
                                   add_goals uu____4067 in
                                 bind uu____4064
                                   (fun uu____4076  ->
                                      let uu____4077 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4077
                                        goal.FStar_Tactics_Types.opts))))))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4083 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4083 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4105 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4105 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___147_4139 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___147_4139.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___147_4139.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4151 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
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
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4180 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4180 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4202 = FStar_Util.set_mem x fns_ty in
           if uu____4202
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4206 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4206
                (fun u  ->
                   let uu____4212 =
                     let uu____4213 = trysolve goal u in
                     Prims.op_Negation uu____4213 in
                   if uu____4212
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___148_4218 = goal in
                        let uu____4219 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4219;
                          FStar_Tactics_Types.goal_ty =
                            (uu___148_4218.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___148_4218.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___148_4218.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4221  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4233 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4233 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4257  ->
                    let uu____4258 = clear b in
                    bind uu____4258
                      (fun uu____4262  ->
                         bind intro (fun uu____4264  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___149_4281 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___149_4281.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___149_4281.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___149_4281.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___149_4281.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4283  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___150_4300 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___150_4300.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___150_4300.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___150_4300.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___150_4300.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4302  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4344 = f x in
          bind uu____4344
            (fun y  ->
               let uu____4352 = mapM f xs in
               bind uu____4352 (fun ys  -> ret (y :: ys)))
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
            let uu____4402 = FStar_Syntax_Subst.compress t in
            uu____4402.FStar_Syntax_Syntax.n in
          let uu____4405 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___152_4411 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___152_4411.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___152_4411.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____4405
            (fun t1  ->
               let tn1 =
                 match tn with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____4448 = ff hd1 in
                     bind uu____4448
                       (fun hd2  ->
                          let fa uu____4468 =
                            match uu____4468 with
                            | (a,q) ->
                                let uu____4481 = ff a in
                                bind uu____4481 (fun a1  -> ret (a1, q)) in
                          let uu____4494 = mapM fa args in
                          bind uu____4494
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____4554 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____4554 with
                      | (bs1,t') ->
                          let uu____4563 =
                            let uu____4566 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____4566 t' in
                          bind uu____4563
                            (fun t''  ->
                               let uu____4570 =
                                 let uu____4571 =
                                   let uu____4588 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____4589 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____4588, uu____4589, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____4571 in
                               ret uu____4570))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____4610 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___151_4617 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___151_4617.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___151_4617.FStar_Syntax_Syntax.vars)
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
            let uu____4651 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4651 with
            | (t1,lcomp,g) ->
                let uu____4663 =
                  (let uu____4666 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____4666) ||
                    (let uu____4668 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4668) in
                if uu____4663
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4675 = new_uvar "pointwise_rec" env typ in
                   bind uu____4675
                     (fun ut  ->
                        log ps
                          (fun uu____4686  ->
                             let uu____4687 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4688 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4687 uu____4688);
                        (let uu____4689 =
                           let uu____4692 =
                             let uu____4693 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4693 typ t1 ut in
                           add_irrelevant_goal "pointwise_rec equation" env
                             uu____4692 opts in
                         bind uu____4689
                           (fun uu____4696  ->
                              let uu____4697 =
                                bind tau
                                  (fun uu____4702  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4697))))
let pointwise:
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____4727 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____4727 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____4764  ->
                     let uu____4765 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____4765);
                bind dismiss_all
                  (fun uu____4768  ->
                     let uu____4769 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____4769
                       (fun gt'  ->
                          log ps
                            (fun uu____4779  ->
                               let uu____4780 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____4780);
                          (let uu____4781 = push_goals gs in
                           bind uu____4781
                             (fun uu____4785  ->
                                add_goals
                                  [(let uu___153_4787 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___153_4787.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___153_4787.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___153_4787.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___153_4787.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4807 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____4807 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4819 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4819 with
            | (hd1,args) ->
                let uu____4852 =
                  let uu____4865 =
                    let uu____4866 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4866.FStar_Syntax_Syntax.n in
                  (uu____4865, args) in
                (match uu____4852 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4880::(l,uu____4882)::(r,uu____4884)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4931 =
                       let uu____4932 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____4932 in
                     if uu____4931
                     then
                       let uu____4935 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____4936 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4935 uu____4936
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____4939) ->
                     let uu____4956 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____4956))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4964 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____4964
         (fun u  ->
            let g' =
              let uu___154_4971 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___154_4971.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___154_4971.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___154_4971.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___154_4971.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____4974  ->
                 let uu____4975 =
                   let uu____4978 =
                     let uu____4979 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4979
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____4978
                     g.FStar_Tactics_Types.opts in
                 bind uu____4975
                   (fun uu____4982  ->
                      let uu____4983 = add_goals [g'] in
                      bind uu____4983 (fun uu____4987  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___155_5004 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___155_5004.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___155_5004.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___155_5004.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___155_5004.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___155_5004.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___155_5004.FStar_Tactics_Types.__dump)
              })
       | uu____5005 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___156_5020 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___156_5020.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___156_5020.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___156_5020.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___156_5020.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___156_5020.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___156_5020.FStar_Tactics_Types.__dump)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5027 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____5053 = __tc g.FStar_Tactics_Types.context t in
         bind uu____5053
           (fun uu____5089  ->
              match uu____5089 with
              | (t1,typ,guard) ->
                  let uu____5105 = FStar_Syntax_Util.head_and_args typ in
                  (match uu____5105 with
                   | (hd1,args) ->
                       let uu____5148 =
                         let uu____5161 =
                           let uu____5162 = FStar_Syntax_Util.un_uinst hd1 in
                           uu____5162.FStar_Syntax_Syntax.n in
                         (uu____5161, args) in
                       (match uu____5148 with
                        | (FStar_Syntax_Syntax.Tm_fvar
                           fv,(p,uu____5181)::(q,uu____5183)::[]) when
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
                              let uu___157_5221 = g in
                              let uu____5222 =
                                FStar_TypeChecker_Env.push_bv
                                  g.FStar_Tactics_Types.context v_p in
                              {
                                FStar_Tactics_Types.context = uu____5222;
                                FStar_Tactics_Types.witness =
                                  (uu___157_5221.FStar_Tactics_Types.witness);
                                FStar_Tactics_Types.goal_ty =
                                  (uu___157_5221.FStar_Tactics_Types.goal_ty);
                                FStar_Tactics_Types.opts =
                                  (uu___157_5221.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___157_5221.FStar_Tactics_Types.is_guard)
                              } in
                            let g2 =
                              let uu___158_5224 = g in
                              let uu____5225 =
                                FStar_TypeChecker_Env.push_bv
                                  g.FStar_Tactics_Types.context v_q in
                              {
                                FStar_Tactics_Types.context = uu____5225;
                                FStar_Tactics_Types.witness =
                                  (uu___158_5224.FStar_Tactics_Types.witness);
                                FStar_Tactics_Types.goal_ty =
                                  (uu___158_5224.FStar_Tactics_Types.goal_ty);
                                FStar_Tactics_Types.opts =
                                  (uu___158_5224.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___158_5224.FStar_Tactics_Types.is_guard)
                              } in
                            bind dismiss
                              (fun uu____5232  ->
                                 let uu____5233 = add_goals [g1; g2] in
                                 bind uu____5233
                                   (fun uu____5242  ->
                                      let uu____5243 =
                                        let uu____5248 =
                                          FStar_Syntax_Syntax.bv_to_name v_p in
                                        let uu____5249 =
                                          FStar_Syntax_Syntax.bv_to_name v_q in
                                        (uu____5248, uu____5249) in
                                      ret uu____5243))
                        | uu____5254 ->
                            let uu____5267 =
                              FStar_TypeChecker_Normalize.term_to_string
                                g.FStar_Tactics_Types.context typ in
                            fail1 "Not a disjunction: %s" uu____5267))))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5290 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5290);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___159_5297 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___159_5297.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___159_5297.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___159_5297.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___159_5297.FStar_Tactics_Types.is_guard)
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
           let uu____5340 = __tc env tm in
           bind uu____5340
             (fun uu____5360  ->
                match uu____5360 with
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
      let uu____5389 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5395 =
              let uu____5396 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5396 in
            new_uvar "uvar_env.2" env uu____5395 in
      bind uu____5389
        (fun typ  ->
           let uu____5408 = new_uvar "uvar_env" env typ in
           bind uu____5408 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____5424 = __tc goal.FStar_Tactics_Types.context t in
         bind uu____5424
           (fun uu____5444  ->
              match uu____5444 with
              | (t1,typ,guard) ->
                  let uu____5456 =
                    let uu____5457 =
                      let uu____5458 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____5458 in
                    Prims.op_Negation uu____5457 in
                  if uu____5456
                  then fail "unshelve: got non-trivial guard"
                  else
                    (let uu____5462 =
                       let uu____5465 =
                         let uu___160_5466 = goal in
                         let uu____5467 =
                           bnorm goal.FStar_Tactics_Types.context t1 in
                         let uu____5468 =
                           bnorm goal.FStar_Tactics_Types.context typ in
                         {
                           FStar_Tactics_Types.context =
                             (uu___160_5466.FStar_Tactics_Types.context);
                           FStar_Tactics_Types.witness = uu____5467;
                           FStar_Tactics_Types.goal_ty = uu____5468;
                           FStar_Tactics_Types.opts =
                             (uu___160_5466.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard = false
                         } in
                       [uu____5465] in
                     add_goals uu____5462)))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5484 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5484)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5504  ->
             let uu____5505 = FStar_Options.unsafe_tactic_exec () in
             if uu____5505
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5511  -> fun uu____5512  -> false) in
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
      let uu____5534 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5534 with
      | (u,uu____5552,g_u) ->
          let g =
            let uu____5567 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5567;
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
      let uu____5584 = goal_of_goal_ty env typ in
      match uu____5584 with
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
              FStar_Tactics_Types.__dump = dump_proofstate
            } in
          (ps, (g.FStar_Tactics_Types.witness))