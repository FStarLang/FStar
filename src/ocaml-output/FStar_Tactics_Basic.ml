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
           (let uu____504 = FStar_Tactics_Types.subst_proof_state subst1 ps in
            dump_cur uu____504 msg);
           FStar_Tactics_Result.Success ((), ps))
let print_proof_state:
  FStar_TypeChecker_Normalize.psc -> Prims.string -> Prims.unit tac =
  fun psc  ->
    fun msg  ->
      mk_tac
        (fun ps  ->
           let subst1 = FStar_TypeChecker_Normalize.psc_subst psc in
           (let uu____523 = FStar_Tactics_Types.subst_proof_state subst1 ps in
            dump_proofstate uu____523 msg);
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
      let uu____554 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____554 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____608 =
              let uu____611 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____611 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____608);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'Auu____701 . Prims.string -> 'Auu____701 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____712 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____712
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____720 . Prims.string -> Prims.string -> 'Auu____720 tac =
  fun msg  ->
    fun x  -> let uu____731 = FStar_Util.format1 msg x in fail uu____731
let fail2:
  'Auu____740 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____740 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____755 = FStar_Util.format2 msg x y in fail uu____755
let fail3:
  'Auu____766 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____766 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____785 = FStar_Util.format3 msg x y z in fail uu____785
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____813 = run t ps in
         match uu____813 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success
                ((FStar_Pervasives_Native.Some a), q))
         | FStar_Tactics_Result.Failed (uu____827,uu____828) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____843  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____861 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____875 =
         let uu___119_876 = p in
         let uu____877 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___119_876.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___119_876.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___119_876.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____877;
           FStar_Tactics_Types.smt_goals =
             (uu___119_876.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___119_876.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___119_876.FStar_Tactics_Types.__dump)
         } in
       set uu____875)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____892 = trysolve goal solution in
      if uu____892
      then dismiss
      else
        (let uu____896 =
           let uu____897 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____898 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____899 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____897 uu____898
             uu____899 in
         fail uu____896)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___120_906 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___120_906.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___120_906.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___120_906.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___120_906.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___120_906.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___120_906.FStar_Tactics_Types.__dump)
          }))
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___121_923 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___121_923.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___121_923.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___121_923.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___121_923.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___121_923.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___121_923.FStar_Tactics_Types.__dump)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___122_940 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___122_940.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___122_940.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___122_940.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___122_940.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___122_940.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___122_940.FStar_Tactics_Types.__dump)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___123_957 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___123_957.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___123_957.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___123_957.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___123_957.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___123_957.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___123_957.FStar_Tactics_Types.__dump)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___124_974 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___124_974.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___124_974.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___124_974.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___124_974.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___124_974.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___124_974.FStar_Tactics_Types.__dump)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____984  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___125_997 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___125_997.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___125_997.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___125_997.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___125_997.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___125_997.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___125_997.FStar_Tactics_Types.__dump)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1026 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1026 with
        | (u,uu____1042,g_u) ->
            let uu____1056 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1056 (fun uu____1060  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1065 = FStar_Syntax_Util.un_squash t in
    match uu____1065 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1075 =
          let uu____1076 = FStar_Syntax_Subst.compress t' in
          uu____1076.FStar_Syntax_Syntax.n in
        (match uu____1075 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1080 -> false)
    | uu____1081 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1090 = FStar_Syntax_Util.un_squash t in
    match uu____1090 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1100 =
          let uu____1101 = FStar_Syntax_Subst.compress t' in
          uu____1101.FStar_Syntax_Syntax.n in
        (match uu____1100 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1105 -> false)
    | uu____1106 -> false
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
          let uu____1144 = new_uvar reason env typ in
          bind uu____1144
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
             let uu____1202 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1202
           with | e1 -> fail "not typeable")
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1244 = __tc goal.FStar_Tactics_Types.context t in
         bind uu____1244
           (fun uu____1264  ->
              match uu____1264 with
              | (t1,typ,guard) ->
                  let uu____1276 =
                    let uu____1277 =
                      let uu____1278 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1278 in
                    Prims.op_Negation uu____1277 in
                  if uu____1276
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
          let uu____1302 = mk_irrelevant_goal reason env phi opts in
          bind uu____1302 (fun goal  -> add_goals [goal])
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
       let uu____1324 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1324
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1328 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1328))
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
          let uu____1349 =
            let uu____1350 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1350.FStar_TypeChecker_Env.guard_f in
          match uu____1349 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1354 = istrivial e f in
              if uu____1354
              then ret ()
              else
                (let uu____1358 = mk_irrelevant_goal reason e f opts in
                 bind uu____1358
                   (fun goal  ->
                      let goal1 =
                        let uu___128_1365 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___128_1365.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___128_1365.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___128_1365.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___128_1365.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard = true
                        } in
                      push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1371 = is_irrelevant g in
       if uu____1371
       then bind dismiss (fun uu____1375  -> add_smt_goals [g])
       else
         (let uu____1377 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1377))
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
             let uu____1423 =
               try
                 let uu____1457 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1457
               with | uu____1487 -> fail "divide: not enough goals" in
             bind uu____1423
               (fun uu____1514  ->
                  match uu____1514 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___129_1540 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___129_1540.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___129_1540.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___129_1540.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___129_1540.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___129_1540.FStar_Tactics_Types.__dump)
                        } in
                      let rp =
                        let uu___130_1542 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___130_1542.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___130_1542.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___130_1542.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___130_1542.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___130_1542.FStar_Tactics_Types.__dump)
                        } in
                      let uu____1543 = set lp in
                      bind uu____1543
                        (fun uu____1551  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1565 = set rp in
                                     bind uu____1565
                                       (fun uu____1573  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___131_1589 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___131_1589.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___131_1589.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___131_1589.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___131_1589.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___131_1589.FStar_Tactics_Types.__dump)
                                                      } in
                                                    let uu____1590 = set p' in
                                                    bind uu____1590
                                                      (fun uu____1598  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1618 = divide (Prims.parse_int "1") f idtac in
    bind uu____1618
      (fun uu____1631  -> match uu____1631 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1666::uu____1667 ->
             let uu____1670 =
               let uu____1679 = map tau in
               divide (Prims.parse_int "1") tau uu____1679 in
             bind uu____1670
               (fun uu____1697  ->
                  match uu____1697 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1736 =
        bind t1
          (fun uu____1741  ->
             let uu____1742 = map t2 in
             bind uu____1742 (fun uu____1750  -> ret ())) in
      focus uu____1736
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1761 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1761 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1776 =
             let uu____1777 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1777 in
           if uu____1776
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1783 = new_uvar "intro" env' typ' in
              bind uu____1783
                (fun u  ->
                   let uu____1790 =
                     let uu____1791 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1791 in
                   if uu____1790
                   then
                     let uu____1794 =
                       let uu____1797 =
                         let uu___134_1798 = goal in
                         let uu____1799 = bnorm env' u in
                         let uu____1800 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1799;
                           FStar_Tactics_Types.goal_ty = uu____1800;
                           FStar_Tactics_Types.opts =
                             (uu___134_1798.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___134_1798.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1797 in
                     bind uu____1794 (fun uu____1802  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1808 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1808)
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
       (let uu____1829 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1829 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1848 =
              let uu____1849 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1849 in
            if uu____1848
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1865 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1865; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1867 =
                 let uu____1870 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____1870 in
               bind uu____1867
                 (fun u  ->
                    let lb =
                      let uu____1886 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____1886 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1890 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1890 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____1927 =
                            let uu____1930 =
                              let uu___135_1931 = goal in
                              let uu____1932 = bnorm env' u in
                              let uu____1933 =
                                let uu____1934 = comp_to_typ c in
                                bnorm env' uu____1934 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____1932;
                                FStar_Tactics_Types.goal_ty = uu____1933;
                                FStar_Tactics_Types.opts =
                                  (uu___135_1931.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___135_1931.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____1930 in
                          bind uu____1927
                            (fun uu____1941  ->
                               let uu____1942 =
                                 let uu____1947 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____1947, b) in
                               ret uu____1942)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____1961 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1961))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____1986 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1986 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___136_1993 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___136_1993.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___136_1993.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___136_1993.FStar_Tactics_Types.is_guard)
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
             let uu____2017 = __tc e t in
             bind uu____2017
               (fun uu____2039  ->
                  match uu____2039 with
                  | (t1,uu____2049,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                       (let steps =
                          let uu____2055 =
                            FStar_TypeChecker_Normalize.tr_norm_steps s in
                          FStar_List.append
                            [FStar_TypeChecker_Normalize.Reify;
                            FStar_TypeChecker_Normalize.UnfoldTac] uu____2055 in
                        let t2 =
                          normalize steps ps.FStar_Tactics_Types.main_context
                            t1 in
                        ret t2))))
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2070 = __tc goal.FStar_Tactics_Types.context t in
         bind uu____2070
           (fun uu____2090  ->
              match uu____2090 with
              | (t1,typ,guard) ->
                  let uu____2102 =
                    let uu____2103 =
                      let uu____2104 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2104 in
                    Prims.op_Negation uu____2103 in
                  if uu____2102
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2108 =
                       do_unify goal.FStar_Tactics_Types.context typ
                         goal.FStar_Tactics_Types.goal_ty in
                     if uu____2108
                     then solve goal t1
                     else
                       (let uu____2112 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context t1 in
                        let uu____2113 =
                          let uu____2114 =
                            bnorm goal.FStar_Tactics_Types.context typ in
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context uu____2114 in
                        let uu____2115 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context
                            goal.FStar_Tactics_Types.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2112 uu____2113 uu____2115))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    mlog
      (fun uu____2126  ->
         let uu____2127 = FStar_Syntax_Print.term_to_string tm in
         FStar_Util.print1 "exact: tm = %s\n" uu____2127)
      (fun uu____2130  -> let uu____2131 = __exact tm in focus uu____2131)
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2146 =
             let uu____2153 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2153 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2146 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2180 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2200 =
               let uu____2205 = __exact tm in trytac uu____2205 in
             bind uu____2200
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2218 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2218 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2250  ->
                                let uu____2251 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2251)
                             (fun uu____2254  ->
                                let uu____2255 =
                                  let uu____2256 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2256 in
                                if uu____2255
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2260 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2260
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2280 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2280 in
                                        let uu____2281 =
                                          __apply uopt tm' typ' in
                                        bind uu____2281
                                          (fun uu____2289  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2291 =
                                               let uu____2292 =
                                                 let uu____2295 =
                                                   let uu____2296 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2296 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2295 in
                                               uu____2292.FStar_Syntax_Syntax.n in
                                             match uu____2291 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2324) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2352 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2352
                                                      then ret ()
                                                      else
                                                        (let uu____2356 =
                                                           let uu____2359 =
                                                             let uu___137_2360
                                                               = goal in
                                                             let uu____2361 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2362 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___137_2360.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2361;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2362;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___137_2360.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2359] in
                                                         add_goals uu____2356))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      mlog
        (fun uu____2415  ->
           let uu____2416 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "apply: tm = %s\n" uu____2416)
        (fun uu____2418  ->
           bind cur_goal
             (fun goal  ->
                let uu____2422 = __tc goal.FStar_Tactics_Types.context tm in
                bind uu____2422
                  (fun uu____2443  ->
                     match uu____2443 with
                     | (tm1,typ,guard) ->
                         let uu____2455 =
                           let uu____2458 =
                             let uu____2461 = __apply uopt tm1 typ in
                             bind uu____2461
                               (fun uu____2465  ->
                                  add_goal_from_guard "apply guard"
                                    goal.FStar_Tactics_Types.context guard
                                    goal.FStar_Tactics_Types.opts) in
                           focus uu____2458 in
                         let uu____2466 =
                           let uu____2469 =
                             FStar_TypeChecker_Normalize.term_to_string
                               goal.FStar_Tactics_Types.context tm1 in
                           let uu____2470 =
                             FStar_TypeChecker_Normalize.term_to_string
                               goal.FStar_Tactics_Types.context typ in
                           let uu____2471 =
                             FStar_TypeChecker_Normalize.term_to_string
                               goal.FStar_Tactics_Types.context
                               goal.FStar_Tactics_Types.goal_ty in
                           fail3
                             "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                             uu____2469 uu____2470 uu____2471 in
                         try_unif uu____2455 uu____2466)))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2480 =
      mlog
        (fun uu____2485  ->
           let uu____2486 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2486)
        (fun uu____2489  ->
           let is_unit_t t =
             let uu____2494 =
               let uu____2495 = FStar_Syntax_Subst.compress t in
               uu____2495.FStar_Syntax_Syntax.n in
             match uu____2494 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid
                 -> true
             | uu____2499 -> false in
           bind cur_goal
             (fun goal  ->
                let uu____2503 = __tc goal.FStar_Tactics_Types.context tm in
                bind uu____2503
                  (fun uu____2525  ->
                     match uu____2525 with
                     | (tm1,t,guard) ->
                         let uu____2537 =
                           FStar_Syntax_Util.arrow_formals_comp t in
                         (match uu____2537 with
                          | (bs,comp) ->
                              if
                                Prims.op_Negation
                                  (FStar_Syntax_Util.is_lemma_comp comp)
                              then fail "apply_lemma: not a lemma"
                              else
                                (let uu____2567 =
                                   FStar_List.fold_left
                                     (fun uu____2613  ->
                                        fun uu____2614  ->
                                          match (uu____2613, uu____2614) with
                                          | ((uvs,guard1,subst1),(b,aq)) ->
                                              let b_t =
                                                FStar_Syntax_Subst.subst
                                                  subst1
                                                  b.FStar_Syntax_Syntax.sort in
                                              let uu____2717 = is_unit_t b_t in
                                              if uu____2717
                                              then
                                                (((FStar_Syntax_Util.exp_unit,
                                                    aq) :: uvs), guard1,
                                                  ((FStar_Syntax_Syntax.NT
                                                      (b,
                                                        FStar_Syntax_Util.exp_unit))
                                                  :: subst1))
                                              else
                                                (let uu____2755 =
                                                   FStar_TypeChecker_Util.new_implicit_var
                                                     "apply_lemma"
                                                     (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                     goal.FStar_Tactics_Types.context
                                                     b_t in
                                                 match uu____2755 with
                                                 | (u,uu____2785,g_u) ->
                                                     let uu____2799 =
                                                       FStar_TypeChecker_Rel.conj_guard
                                                         guard1 g_u in
                                                     (((u, aq) :: uvs),
                                                       uu____2799,
                                                       ((FStar_Syntax_Syntax.NT
                                                           (b, u)) ::
                                                       subst1))))
                                     ([], guard, []) bs in
                                 match uu____2567 with
                                 | (uvs,implicits,subst1) ->
                                     let uvs1 = FStar_List.rev uvs in
                                     let comp1 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp in
                                     let uu____2869 =
                                       let uu____2878 =
                                         let uu____2887 =
                                           FStar_Syntax_Util.comp_to_comp_typ
                                             comp1 in
                                         uu____2887.FStar_Syntax_Syntax.effect_args in
                                       match uu____2878 with
                                       | pre::post::uu____2898 ->
                                           ((FStar_Pervasives_Native.fst pre),
                                             (FStar_Pervasives_Native.fst
                                                post))
                                       | uu____2939 ->
                                           failwith
                                             "apply_lemma: impossible: not a lemma" in
                                     (match uu____2869 with
                                      | (pre,post) ->
                                          let uu____2968 =
                                            let uu____2969 =
                                              let uu____2970 =
                                                FStar_Syntax_Util.mk_squash
                                                  post in
                                              do_unify
                                                goal.FStar_Tactics_Types.context
                                                uu____2970
                                                goal.FStar_Tactics_Types.goal_ty in
                                            Prims.op_Negation uu____2969 in
                                          if uu____2968
                                          then
                                            let uu____2973 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                goal.FStar_Tactics_Types.context
                                                tm1 in
                                            let uu____2974 =
                                              let uu____2975 =
                                                FStar_Syntax_Util.mk_squash
                                                  post in
                                              FStar_TypeChecker_Normalize.term_to_string
                                                goal.FStar_Tactics_Types.context
                                                uu____2975 in
                                            let uu____2976 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                goal.FStar_Tactics_Types.context
                                                goal.FStar_Tactics_Types.goal_ty in
                                            fail3
                                              "apply_lemma: Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                              uu____2973 uu____2974
                                              uu____2976
                                          else
                                            (let solution =
                                               let uu____2979 =
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   tm1 uvs1
                                                   FStar_Pervasives_Native.None
                                                   (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                               FStar_TypeChecker_Normalize.normalize
                                                 [FStar_TypeChecker_Normalize.Beta]
                                                 goal.FStar_Tactics_Types.context
                                                 uu____2979 in
                                             let uu____2980 =
                                               add_implicits
                                                 implicits.FStar_TypeChecker_Env.implicits in
                                             bind uu____2980
                                               (fun uu____2986  ->
                                                  let implicits1 =
                                                    FStar_All.pipe_right
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                      (FStar_List.filter
                                                         (fun uu____3054  ->
                                                            match uu____3054
                                                            with
                                                            | (uu____3067,uu____3068,uu____3069,tm2,uu____3071,uu____3072)
                                                                ->
                                                                let uu____3073
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    tm2 in
                                                                (match uu____3073
                                                                 with
                                                                 | (hd1,uu____3089)
                                                                    ->
                                                                    let uu____3110
                                                                    =
                                                                    let uu____3111
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3111.FStar_Syntax_Syntax.n in
                                                                    (match uu____3110
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3114
                                                                    -> true
                                                                    | 
                                                                    uu____3131
                                                                    -> false)))) in
                                                  let uu____3132 =
                                                    solve goal solution in
                                                  bind uu____3132
                                                    (fun uu____3143  ->
                                                       let is_free_uvar uv t1
                                                         =
                                                         let free_uvars =
                                                           let uu____3154 =
                                                             let uu____3161 =
                                                               FStar_Syntax_Free.uvars
                                                                 t1 in
                                                             FStar_Util.set_elements
                                                               uu____3161 in
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.fst
                                                             uu____3154 in
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
                                                         let uu____3202 =
                                                           FStar_Syntax_Util.head_and_args
                                                             t1 in
                                                         match uu____3202
                                                         with
                                                         | (hd1,uu____3218)
                                                             ->
                                                             (match hd1.FStar_Syntax_Syntax.n
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_uvar
                                                                  (uv,uu____3240)
                                                                  ->
                                                                  appears uv
                                                                    goals
                                                              | uu____3265 ->
                                                                  false) in
                                                       let sub_goals =
                                                         FStar_All.pipe_right
                                                           implicits1
                                                           (FStar_List.map
                                                              (fun uu____3307
                                                                  ->
                                                                 match uu____3307
                                                                 with
                                                                 | (_msg,_env,_uvar,term,typ,uu____3325)
                                                                    ->
                                                                    let uu___140_3326
                                                                    = goal in
                                                                    let uu____3327
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3328
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___140_3326.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3327;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3328;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___140_3326.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___140_3326.FStar_Tactics_Types.is_guard)
                                                                    })) in
                                                       let rec filter' f xs =
                                                         match xs with
                                                         | [] -> []
                                                         | x::xs1 ->
                                                             let uu____3366 =
                                                               f x xs1 in
                                                             if uu____3366
                                                             then
                                                               let uu____3369
                                                                 =
                                                                 filter' f
                                                                   xs1 in
                                                               x ::
                                                                 uu____3369
                                                             else
                                                               filter' f xs1 in
                                                       let sub_goals1 =
                                                         filter'
                                                           (fun g  ->
                                                              fun goals  ->
                                                                let uu____3383
                                                                  =
                                                                  checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                Prims.op_Negation
                                                                  uu____3383)
                                                           sub_goals in
                                                       let uu____3384 =
                                                         add_goal_from_guard
                                                           "apply_lemma guard"
                                                           goal.FStar_Tactics_Types.context
                                                           guard
                                                           goal.FStar_Tactics_Types.opts in
                                                       bind uu____3384
                                                         (fun uu____3389  ->
                                                            let uu____3390 =
                                                              let uu____3393
                                                                =
                                                                let uu____3394
                                                                  =
                                                                  let uu____3395
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                  istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____3395 in
                                                                Prims.op_Negation
                                                                  uu____3394 in
                                                              if uu____3393
                                                              then
                                                                add_irrelevant_goal
                                                                  "apply_lemma precondition"
                                                                  goal.FStar_Tactics_Types.context
                                                                  pre
                                                                  goal.FStar_Tactics_Types.opts
                                                              else ret () in
                                                            bind uu____3390
                                                              (fun uu____3400
                                                                  ->
                                                                 add_goals
                                                                   sub_goals1))))))))))) in
    focus uu____2480
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3417 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3417 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3427::(e1,uu____3429)::(e2,uu____3431)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3490 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3513 = destruct_eq' typ in
    match uu____3513 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3543 = FStar_Syntax_Util.un_squash typ in
        (match uu____3543 with
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
        let uu____3601 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3601 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3649 = aux e' in
               FStar_Util.map_opt uu____3649
                 (fun uu____3673  ->
                    match uu____3673 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3694 = aux e in
      FStar_Util.map_opt uu____3694
        (fun uu____3718  ->
           match uu____3718 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____3779 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____3779
            (fun uu____3803  ->
               match uu____3803 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___141_3820 = bv in
                     let uu____3821 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___141_3820.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___141_3820.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3821
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___142_3830 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___142_3830.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___142_3830.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3844 = h in
         match uu____3844 with
         | (bv,uu____3848) ->
             mlog
               (fun uu____3852  ->
                  let uu____3853 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____3854 =
                    FStar_Syntax_Print.term_to_string
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3853
                    uu____3854)
               (fun uu____3857  ->
                  let uu____3858 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____3858 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____3887 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____3887 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____3902 =
                             let uu____3903 = FStar_Syntax_Subst.compress x in
                             uu____3903.FStar_Syntax_Syntax.n in
                           (match uu____3902 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___143_3916 = bv1 in
                                  let uu____3917 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___143_3916.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___143_3916.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____3917
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____3923 =
                                  let uu___144_3924 = goal in
                                  let uu____3925 = push_bvs e0 (bv :: bvs1) in
                                  let uu____3926 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____3927 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____3925;
                                    FStar_Tactics_Types.witness = uu____3926;
                                    FStar_Tactics_Types.goal_ty = uu____3927;
                                    FStar_Tactics_Types.opts =
                                      (uu___144_3924.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___144_3924.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____3923
                            | uu____3928 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____3929 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3956 = b in
           match uu____3956 with
           | (bv,uu____3960) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___145_3964 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___145_3964.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___145_3964.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3968 =
                   let uu____3969 =
                     let uu____3976 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3976) in
                   FStar_Syntax_Syntax.NT uu____3969 in
                 [uu____3968] in
               let uu____3977 = subst_goal bv bv' s1 goal in
               (match uu____3977 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____3997 = b in
         match uu____3997 with
         | (bv,uu____4001) ->
             let uu____4002 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4002 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4031 = FStar_Syntax_Util.type_u () in
                  (match uu____4031 with
                   | (ty,u) ->
                       let uu____4040 = new_uvar "binder_retype" e0 ty in
                       bind uu____4040
                         (fun t'  ->
                            let bv'' =
                              let uu___146_4050 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___146_4050.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___146_4050.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4054 =
                                let uu____4055 =
                                  let uu____4062 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4062) in
                                FStar_Syntax_Syntax.NT uu____4055 in
                              [uu____4054] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___147_4070 = b1 in
                                   let uu____4071 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___147_4070.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___147_4070.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4071
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4077  ->
                                 let uu____4078 =
                                   let uu____4081 =
                                     let uu____4084 =
                                       let uu___148_4085 = goal in
                                       let uu____4086 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4087 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4086;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4087;
                                         FStar_Tactics_Types.opts =
                                           (uu___148_4085.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___148_4085.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4084] in
                                   add_goals uu____4081 in
                                 bind uu____4078
                                   (fun uu____4090  ->
                                      let uu____4091 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4091
                                        goal.FStar_Tactics_Types.opts))))))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4097 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4097 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4119 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4119 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___149_4153 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___149_4153.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___149_4153.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4165 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4165 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4186 = FStar_Syntax_Print.bv_to_string x in
               let uu____4187 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4186 uu____4187
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4194 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4194 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4216 = FStar_Util.set_mem x fns_ty in
           if uu____4216
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4220 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4220
                (fun u  ->
                   let uu____4226 =
                     let uu____4227 = trysolve goal u in
                     Prims.op_Negation uu____4227 in
                   if uu____4226
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___150_4232 = goal in
                        let uu____4233 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4233;
                          FStar_Tactics_Types.goal_ty =
                            (uu___150_4232.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___150_4232.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___150_4232.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4235  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4247 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4247 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4271  ->
                    let uu____4272 = clear b in
                    bind uu____4272
                      (fun uu____4276  ->
                         bind intro (fun uu____4278  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___151_4295 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___151_4295.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___151_4295.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___151_4295.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___151_4295.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4297  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___152_4314 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___152_4314.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___152_4314.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___152_4314.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___152_4314.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4316  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4358 = f x in
          bind uu____4358
            (fun y  ->
               let uu____4366 = mapM f xs in
               bind uu____4366 (fun ys  -> ret (y :: ys)))
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
            let uu____4416 = FStar_Syntax_Subst.compress t in
            uu____4416.FStar_Syntax_Syntax.n in
          let uu____4419 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___154_4425 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___154_4425.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___154_4425.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____4419
            (fun t1  ->
               let tn1 =
                 match tn with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____4462 = ff hd1 in
                     bind uu____4462
                       (fun hd2  ->
                          let fa uu____4482 =
                            match uu____4482 with
                            | (a,q) ->
                                let uu____4495 = ff a in
                                bind uu____4495 (fun a1  -> ret (a1, q)) in
                          let uu____4508 = mapM fa args in
                          bind uu____4508
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____4568 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____4568 with
                      | (bs1,t') ->
                          let uu____4577 =
                            let uu____4580 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____4580 t' in
                          bind uu____4577
                            (fun t''  ->
                               let uu____4584 =
                                 let uu____4585 =
                                   let uu____4602 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____4603 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____4602, uu____4603, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____4585 in
                               ret uu____4584))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____4624 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___153_4631 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___153_4631.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___153_4631.FStar_Syntax_Syntax.vars)
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
            let uu____4665 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4665 with
            | (t1,lcomp,g) ->
                let uu____4677 =
                  (let uu____4680 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____4680) ||
                    (let uu____4682 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4682) in
                if uu____4677
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4689 = new_uvar "pointwise_rec" env typ in
                   bind uu____4689
                     (fun ut  ->
                        log ps
                          (fun uu____4700  ->
                             let uu____4701 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4702 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4701 uu____4702);
                        (let uu____4703 =
                           let uu____4706 =
                             let uu____4707 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4707 typ t1 ut in
                           add_irrelevant_goal "pointwise_rec equation" env
                             uu____4706 opts in
                         bind uu____4703
                           (fun uu____4710  ->
                              let uu____4711 =
                                bind tau
                                  (fun uu____4716  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4711))))
let pointwise:
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____4741 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____4741 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____4778  ->
                     let uu____4779 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____4779);
                bind dismiss_all
                  (fun uu____4782  ->
                     let uu____4783 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____4783
                       (fun gt'  ->
                          log ps
                            (fun uu____4793  ->
                               let uu____4794 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____4794);
                          (let uu____4795 = push_goals gs in
                           bind uu____4795
                             (fun uu____4799  ->
                                add_goals
                                  [(let uu___155_4801 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___155_4801.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___155_4801.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___155_4801.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___155_4801.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4821 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____4821 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4833 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4833 with
            | (hd1,args) ->
                let uu____4866 =
                  let uu____4879 =
                    let uu____4880 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4880.FStar_Syntax_Syntax.n in
                  (uu____4879, args) in
                (match uu____4866 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4894::(l,uu____4896)::(r,uu____4898)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4945 =
                       let uu____4946 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____4946 in
                     if uu____4945
                     then
                       let uu____4949 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____4950 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4949 uu____4950
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____4953) ->
                     let uu____4970 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____4970))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4978 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____4978
         (fun u  ->
            let g' =
              let uu___156_4985 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___156_4985.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___156_4985.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___156_4985.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___156_4985.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____4988  ->
                 let uu____4989 =
                   let uu____4992 =
                     let uu____4993 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4993
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____4992
                     g.FStar_Tactics_Types.opts in
                 bind uu____4989
                   (fun uu____4996  ->
                      let uu____4997 = add_goals [g'] in
                      bind uu____4997 (fun uu____5001  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___157_5018 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___157_5018.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___157_5018.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___157_5018.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___157_5018.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___157_5018.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___157_5018.FStar_Tactics_Types.__dump)
              })
       | uu____5019 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___158_5034 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___158_5034.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___158_5034.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___158_5034.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___158_5034.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___158_5034.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___158_5034.FStar_Tactics_Types.__dump)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5041 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____5067 = __tc g.FStar_Tactics_Types.context t in
         bind uu____5067
           (fun uu____5103  ->
              match uu____5103 with
              | (t1,typ,guard) ->
                  let uu____5119 = FStar_Syntax_Util.head_and_args typ in
                  (match uu____5119 with
                   | (hd1,args) ->
                       let uu____5162 =
                         let uu____5175 =
                           let uu____5176 = FStar_Syntax_Util.un_uinst hd1 in
                           uu____5176.FStar_Syntax_Syntax.n in
                         (uu____5175, args) in
                       (match uu____5162 with
                        | (FStar_Syntax_Syntax.Tm_fvar
                           fv,(p,uu____5195)::(q,uu____5197)::[]) when
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
                              let uu___159_5235 = g in
                              let uu____5236 =
                                FStar_TypeChecker_Env.push_bv
                                  g.FStar_Tactics_Types.context v_p in
                              {
                                FStar_Tactics_Types.context = uu____5236;
                                FStar_Tactics_Types.witness =
                                  (uu___159_5235.FStar_Tactics_Types.witness);
                                FStar_Tactics_Types.goal_ty =
                                  (uu___159_5235.FStar_Tactics_Types.goal_ty);
                                FStar_Tactics_Types.opts =
                                  (uu___159_5235.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___159_5235.FStar_Tactics_Types.is_guard)
                              } in
                            let g2 =
                              let uu___160_5238 = g in
                              let uu____5239 =
                                FStar_TypeChecker_Env.push_bv
                                  g.FStar_Tactics_Types.context v_q in
                              {
                                FStar_Tactics_Types.context = uu____5239;
                                FStar_Tactics_Types.witness =
                                  (uu___160_5238.FStar_Tactics_Types.witness);
                                FStar_Tactics_Types.goal_ty =
                                  (uu___160_5238.FStar_Tactics_Types.goal_ty);
                                FStar_Tactics_Types.opts =
                                  (uu___160_5238.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___160_5238.FStar_Tactics_Types.is_guard)
                              } in
                            bind dismiss
                              (fun uu____5246  ->
                                 let uu____5247 = add_goals [g1; g2] in
                                 bind uu____5247
                                   (fun uu____5256  ->
                                      let uu____5257 =
                                        let uu____5262 =
                                          FStar_Syntax_Syntax.bv_to_name v_p in
                                        let uu____5263 =
                                          FStar_Syntax_Syntax.bv_to_name v_q in
                                        (uu____5262, uu____5263) in
                                      ret uu____5257))
                        | uu____5268 ->
                            let uu____5281 =
                              FStar_TypeChecker_Normalize.term_to_string
                                g.FStar_Tactics_Types.context typ in
                            fail1 "Not a disjunction: %s" uu____5281))))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5304 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5304);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___161_5311 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___161_5311.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___161_5311.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___161_5311.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___161_5311.FStar_Tactics_Types.is_guard)
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
           let uu____5354 = __tc env tm in
           bind uu____5354
             (fun uu____5374  ->
                match uu____5374 with
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
      let uu____5403 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5409 =
              let uu____5410 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5410 in
            new_uvar "uvar_env.2" env uu____5409 in
      bind uu____5403
        (fun typ  ->
           let uu____5422 = new_uvar "uvar_env" env typ in
           bind uu____5422 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____5438 = __tc goal.FStar_Tactics_Types.context t in
         bind uu____5438
           (fun uu____5458  ->
              match uu____5458 with
              | (t1,typ,guard) ->
                  let uu____5470 =
                    let uu____5471 =
                      let uu____5472 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____5472 in
                    Prims.op_Negation uu____5471 in
                  if uu____5470
                  then fail "unshelve: got non-trivial guard"
                  else
                    (let uu____5476 =
                       let uu____5479 =
                         let uu___162_5480 = goal in
                         let uu____5481 =
                           bnorm goal.FStar_Tactics_Types.context t1 in
                         let uu____5482 =
                           bnorm goal.FStar_Tactics_Types.context typ in
                         {
                           FStar_Tactics_Types.context =
                             (uu___162_5480.FStar_Tactics_Types.context);
                           FStar_Tactics_Types.witness = uu____5481;
                           FStar_Tactics_Types.goal_ty = uu____5482;
                           FStar_Tactics_Types.opts =
                             (uu___162_5480.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard = false
                         } in
                       [uu____5479] in
                     add_goals uu____5476)))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5498 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5498)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5518  ->
             let uu____5519 = FStar_Options.unsafe_tactic_exec () in
             if uu____5519
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5525  -> fun uu____5526  -> false) in
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
      let uu____5548 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5548 with
      | (u,uu____5566,g_u) ->
          let g =
            let uu____5581 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5581;
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
      let uu____5598 = goal_of_goal_ty env typ in
      match uu____5598 with
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