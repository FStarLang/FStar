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
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail: 'Auu____669 . Prims.string -> 'Auu____669 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____680 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____680
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____688 . Prims.string -> Prims.string -> 'Auu____688 tac =
  fun msg  ->
    fun x  -> let uu____699 = FStar_Util.format1 msg x in fail uu____699
let fail2:
  'Auu____708 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____708 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____723 = FStar_Util.format2 msg x y in fail uu____723
let fail3:
  'Auu____734 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____734 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____753 = FStar_Util.format3 msg x y z in fail uu____753
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____781 = run t ps in
         match uu____781 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success
                ((FStar_Pervasives_Native.Some a), q))
         | FStar_Tactics_Result.Failed (uu____795,uu____796) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____811  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____829 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____843 =
         let uu___92_844 = p in
         let uu____845 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___92_844.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___92_844.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___92_844.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____845;
           FStar_Tactics_Types.smt_goals =
             (uu___92_844.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___92_844.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___92_844.FStar_Tactics_Types.__dump)
         } in
       set uu____843)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____860 = trysolve goal solution in
      if uu____860
      then dismiss
      else
        (let uu____864 =
           let uu____865 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____866 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____867 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____865 uu____866
             uu____867 in
         fail uu____864)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___93_874 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___93_874.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___93_874.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___93_874.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___93_874.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___93_874.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___93_874.FStar_Tactics_Types.__dump)
          }))
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___94_891 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___94_891.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___94_891.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___94_891.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___94_891.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___94_891.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___94_891.FStar_Tactics_Types.__dump)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___95_908 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___95_908.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___95_908.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___95_908.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___95_908.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___95_908.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___95_908.FStar_Tactics_Types.__dump)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___96_925 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___96_925.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___96_925.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___96_925.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___96_925.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___96_925.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___96_925.FStar_Tactics_Types.__dump)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___97_942 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___97_942.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___97_942.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___97_942.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___97_942.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___97_942.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___97_942.FStar_Tactics_Types.__dump)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____952  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___98_965 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___98_965.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___98_965.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___98_965.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___98_965.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___98_965.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___98_965.FStar_Tactics_Types.__dump)
            }))
let new_uvar: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun typ  ->
      let uu____990 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____990 with
      | (u,uu____1006,g_u) ->
          let uu____1020 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____1020 (fun uu____1024  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1029 = FStar_Syntax_Util.un_squash t in
    match uu____1029 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1039 =
          let uu____1040 = FStar_Syntax_Subst.compress t' in
          uu____1040.FStar_Syntax_Syntax.n in
        (match uu____1039 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1044 -> false)
    | uu____1045 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1054 = FStar_Syntax_Util.un_squash t in
    match uu____1054 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1064 =
          let uu____1065 = FStar_Syntax_Subst.compress t' in
          uu____1065.FStar_Syntax_Syntax.n in
        (match uu____1064 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1069 -> false)
    | uu____1070 -> false
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
        let uu____1104 = new_uvar env typ in
        bind uu____1104
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
        let uu____1127 = mk_irrelevant_goal env phi opts in
        bind uu____1127 (fun goal  -> add_goals [goal])
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
       let uu____1149 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1149
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1153 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1153))
let add_goal_from_guard:
  env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Options.optionstate -> Prims.unit tac
  =
  fun e  ->
    fun g  ->
      fun opts  ->
        let uu____1170 =
          let uu____1171 = FStar_TypeChecker_Rel.simplify_guard e g in
          uu____1171.FStar_TypeChecker_Env.guard_f in
        match uu____1170 with
        | FStar_TypeChecker_Common.Trivial  -> ret ()
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____1175 = istrivial e f in
            if uu____1175
            then ret ()
            else
              (let uu____1179 = mk_irrelevant_goal e f opts in
               bind uu____1179
                 (fun goal  ->
                    let goal1 =
                      let uu___99_1186 = goal in
                      {
                        FStar_Tactics_Types.context =
                          (uu___99_1186.FStar_Tactics_Types.context);
                        FStar_Tactics_Types.witness =
                          (uu___99_1186.FStar_Tactics_Types.witness);
                        FStar_Tactics_Types.goal_ty =
                          (uu___99_1186.FStar_Tactics_Types.goal_ty);
                        FStar_Tactics_Types.opts =
                          (uu___99_1186.FStar_Tactics_Types.opts);
                        FStar_Tactics_Types.is_guard = true
                      } in
                    push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1192 = is_irrelevant g in
       if uu____1192
       then bind dismiss (fun uu____1196  -> add_smt_goals [g])
       else
         (let uu____1198 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1198))
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
             let uu____1244 =
               try
                 let uu____1278 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1278
               with | uu____1308 -> fail "divide: not enough goals" in
             bind uu____1244
               (fun uu____1335  ->
                  match uu____1335 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___100_1361 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___100_1361.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___100_1361.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___100_1361.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___100_1361.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___100_1361.FStar_Tactics_Types.__dump)
                        } in
                      let rp =
                        let uu___101_1363 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___101_1363.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___101_1363.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___101_1363.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___101_1363.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___101_1363.FStar_Tactics_Types.__dump)
                        } in
                      let uu____1364 = set lp in
                      bind uu____1364
                        (fun uu____1372  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1386 = set rp in
                                     bind uu____1386
                                       (fun uu____1394  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___102_1410 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___102_1410.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___102_1410.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___102_1410.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___102_1410.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___102_1410.FStar_Tactics_Types.__dump)
                                                      } in
                                                    let uu____1411 = set p' in
                                                    bind uu____1411
                                                      (fun uu____1419  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1439 = divide (Prims.parse_int "1") f idtac in
    bind uu____1439
      (fun uu____1452  -> match uu____1452 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1487::uu____1488 ->
             let uu____1491 =
               let uu____1500 = map tau in
               divide (Prims.parse_int "1") tau uu____1500 in
             bind uu____1491
               (fun uu____1518  ->
                  match uu____1518 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1557 =
        bind t1
          (fun uu____1562  ->
             let uu____1563 = map t2 in
             bind uu____1563 (fun uu____1571  -> ret ())) in
      focus uu____1557
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1582 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1582 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1597 =
             let uu____1598 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1598 in
           if uu____1597
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1604 = new_uvar env' typ' in
              bind uu____1604
                (fun u  ->
                   let uu____1611 =
                     let uu____1612 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1612 in
                   if uu____1611
                   then
                     let uu____1615 =
                       let uu____1618 =
                         let uu___105_1619 = goal in
                         let uu____1620 = bnorm env' u in
                         let uu____1621 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1620;
                           FStar_Tactics_Types.goal_ty = uu____1621;
                           FStar_Tactics_Types.opts =
                             (uu___105_1619.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___105_1619.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1618 in
                     bind uu____1615 (fun uu____1623  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1629 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1629)
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
       (let uu____1650 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1650 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1669 =
              let uu____1670 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1670 in
            if uu____1669
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1686 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1686; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1688 =
                 let uu____1691 = comp_to_typ c in new_uvar env' uu____1691 in
               bind uu____1688
                 (fun u  ->
                    let lb =
                      let uu____1707 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____1707 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1711 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1711 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____1748 =
                            let uu____1751 =
                              let uu___106_1752 = goal in
                              let uu____1753 = bnorm env' u in
                              let uu____1754 =
                                let uu____1755 = comp_to_typ c in
                                bnorm env' uu____1755 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____1753;
                                FStar_Tactics_Types.goal_ty = uu____1754;
                                FStar_Tactics_Types.opts =
                                  (uu___106_1752.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___106_1752.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____1751 in
                          bind uu____1748
                            (fun uu____1762  ->
                               let uu____1763 =
                                 let uu____1768 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____1768, b) in
                               ret uu____1763)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____1782 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1782))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____1807 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1807 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___107_1814 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___107_1814.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___107_1814.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___107_1814.FStar_Tactics_Types.is_guard)
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
             let uu____1838 = FStar_TypeChecker_Normalize.tr_norm_steps s in
             FStar_List.append
               [FStar_TypeChecker_Normalize.Reify;
               FStar_TypeChecker_Normalize.UnfoldTac] uu____1838 in
           let t1 = normalize steps ps.FStar_Tactics_Types.main_context t in
           ret t1)
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1853 =
           try
             let uu____1881 =
               (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
                 goal.FStar_Tactics_Types.context t in
             ret uu____1881
           with
           | e ->
               let uu____1908 = FStar_Syntax_Print.term_to_string t in
               let uu____1909 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1908
                 uu____1909 in
         bind uu____1853
           (fun uu____1927  ->
              match uu____1927 with
              | (t1,typ,guard) ->
                  let uu____1939 =
                    let uu____1940 =
                      let uu____1941 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1941 in
                    Prims.op_Negation uu____1940 in
                  if uu____1939
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1945 =
                       do_unify goal.FStar_Tactics_Types.context typ
                         goal.FStar_Tactics_Types.goal_ty in
                     if uu____1945
                     then solve goal t1
                     else
                       (let uu____1949 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context t1 in
                        let uu____1950 =
                          let uu____1951 =
                            bnorm goal.FStar_Tactics_Types.context typ in
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context uu____1951 in
                        let uu____1952 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context
                            goal.FStar_Tactics_Types.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1949 uu____1950 uu____1952))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  -> let uu____1961 = __exact t in focus uu____1961
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1975 =
           try
             let uu____2003 =
               FStar_TypeChecker_TcTerm.tc_term
                 goal.FStar_Tactics_Types.context t in
             ret uu____2003
           with
           | e ->
               let uu____2030 = FStar_Syntax_Print.term_to_string t in
               let uu____2031 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2030
                 uu____2031 in
         bind uu____1975
           (fun uu____2049  ->
              match uu____2049 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2067 =
                       let uu____2068 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2068 in
                     if uu____2067
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2072 =
                          let uu____2081 =
                            let uu____2090 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2090.FStar_Syntax_Syntax.effect_args in
                          match uu____2081 with
                          | pre::post::uu____2101 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2142 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2072 with
                        | (pre,post) ->
                            let uu____2171 =
                              do_unify goal.FStar_Tactics_Types.context post
                                goal.FStar_Tactics_Types.goal_ty in
                            if uu____2171
                            then
                              let uu____2174 = solve goal t1 in
                              bind uu____2174
                                (fun uu____2178  ->
                                   add_irrelevant_goal
                                     goal.FStar_Tactics_Types.context pre
                                     goal.FStar_Tactics_Types.opts)
                            else
                              (let uu____2180 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context t1 in
                               let uu____2181 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context post in
                               let uu____2182 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2180 uu____2181 uu____2182)))))
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2195 =
             let uu____2202 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2202 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2195 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2229 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2249 =
               let uu____2254 = __exact tm in trytac uu____2254 in
             bind uu____2249
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2267 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2267 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           let uu____2297 =
                             let uu____2298 =
                               FStar_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu____2298 in
                           if uu____2297
                           then fail "apply: not total codomain"
                           else
                             (let uu____2302 =
                                new_uvar goal.FStar_Tactics_Types.context
                                  bv.FStar_Syntax_Syntax.sort in
                              bind uu____2302
                                (fun u  ->
                                   let tm' =
                                     FStar_Syntax_Syntax.mk_Tm_app tm
                                       [(u, aq)] FStar_Pervasives_Native.None
                                       (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                   let typ' =
                                     let uu____2322 = comp_to_typ c in
                                     FStar_All.pipe_left
                                       (FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.NT (bv, u)])
                                       uu____2322 in
                                   let uu____2323 = __apply uopt tm' typ' in
                                   bind uu____2323
                                     (fun uu____2331  ->
                                        let u1 =
                                          bnorm
                                            goal.FStar_Tactics_Types.context
                                            u in
                                        let uu____2333 =
                                          let uu____2334 =
                                            let uu____2337 =
                                              let uu____2338 =
                                                FStar_Syntax_Util.head_and_args
                                                  u1 in
                                              FStar_Pervasives_Native.fst
                                                uu____2338 in
                                            FStar_Syntax_Subst.compress
                                              uu____2337 in
                                          uu____2334.FStar_Syntax_Syntax.n in
                                        match uu____2333 with
                                        | FStar_Syntax_Syntax.Tm_uvar
                                            (uvar,uu____2366) ->
                                            bind get
                                              (fun ps  ->
                                                 let uu____2394 =
                                                   uopt &&
                                                     (uvar_free uvar ps) in
                                                 if uu____2394
                                                 then ret ()
                                                 else
                                                   (let uu____2398 =
                                                      let uu____2401 =
                                                        let uu___112_2402 =
                                                          goal in
                                                        let uu____2403 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            u1 in
                                                        let uu____2404 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          FStar_Tactics_Types.context
                                                            =
                                                            (uu___112_2402.FStar_Tactics_Types.context);
                                                          FStar_Tactics_Types.witness
                                                            = uu____2403;
                                                          FStar_Tactics_Types.goal_ty
                                                            = uu____2404;
                                                          FStar_Tactics_Types.opts
                                                            =
                                                            (uu___112_2402.FStar_Tactics_Types.opts);
                                                          FStar_Tactics_Types.is_guard
                                                            = false
                                                        } in
                                                      [uu____2401] in
                                                    add_goals uu____2398))
                                        | t -> ret ()))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2463 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2463 with
           | (tm1,typ,guard) ->
               let uu____2475 =
                 let uu____2478 =
                   let uu____2481 = __apply uopt tm1 typ in
                   bind uu____2481
                     (fun uu____2485  ->
                        add_goal_from_guard goal.FStar_Tactics_Types.context
                          guard goal.FStar_Tactics_Types.opts) in
                 focus uu____2478 in
               let uu____2486 =
                 let uu____2489 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context tm1 in
                 let uu____2490 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context typ in
                 let uu____2491 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context
                     goal.FStar_Tactics_Types.goal_ty in
                 fail3
                   "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                   uu____2489 uu____2490 uu____2491 in
               try_unif uu____2475 uu____2486)
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2500 =
      let is_unit_t t =
        let uu____2507 =
          let uu____2508 = FStar_Syntax_Subst.compress t in
          uu____2508.FStar_Syntax_Syntax.n in
        match uu____2507 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
            true
        | uu____2512 -> false in
      bind cur_goal
        (fun goal  ->
           let uu____2522 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2522 with
           | (tm1,t,guard) ->
               let uu____2534 = FStar_Syntax_Util.arrow_formals_comp t in
               (match uu____2534 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2564 =
                         FStar_List.fold_left
                           (fun uu____2610  ->
                              fun uu____2611  ->
                                match (uu____2610, uu____2611) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2714 = is_unit_t b_t in
                                    if uu____2714
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____2752 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.FStar_Tactics_Types.context
                                           b_t in
                                       match uu____2752 with
                                       | (u,uu____2782,g_u) ->
                                           let uu____2796 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____2796,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2564 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____2866 =
                             let uu____2875 =
                               let uu____2884 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____2884.FStar_Syntax_Syntax.effect_args in
                             match uu____2875 with
                             | pre::post::uu____2895 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____2936 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____2866 with
                            | (pre,post) ->
                                let uu____2965 =
                                  let uu____2966 =
                                    let uu____2967 =
                                      FStar_Syntax_Util.mk_squash post in
                                    do_unify goal.FStar_Tactics_Types.context
                                      uu____2967
                                      goal.FStar_Tactics_Types.goal_ty in
                                  Prims.op_Negation uu____2966 in
                                if uu____2965
                                then
                                  let uu____2970 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context tm1 in
                                  let uu____2971 =
                                    let uu____2972 =
                                      FStar_Syntax_Util.mk_squash post in
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context
                                      uu____2972 in
                                  let uu____2973 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context
                                      goal.FStar_Tactics_Types.goal_ty in
                                  fail3
                                    "apply_lemma: Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                    uu____2970 uu____2971 uu____2973
                                else
                                  (let solution =
                                     let uu____2976 =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       goal.FStar_Tactics_Types.context
                                       uu____2976 in
                                   let implicits1 =
                                     FStar_All.pipe_right
                                       implicits.FStar_TypeChecker_Env.implicits
                                       (FStar_List.filter
                                          (fun uu____3044  ->
                                             match uu____3044 with
                                             | (uu____3057,uu____3058,uu____3059,tm2,uu____3061,uu____3062)
                                                 ->
                                                 let uu____3063 =
                                                   FStar_Syntax_Util.head_and_args
                                                     tm2 in
                                                 (match uu____3063 with
                                                  | (hd1,uu____3079) ->
                                                      let uu____3100 =
                                                        let uu____3101 =
                                                          FStar_Syntax_Subst.compress
                                                            hd1 in
                                                        uu____3101.FStar_Syntax_Syntax.n in
                                                      (match uu____3100 with
                                                       | FStar_Syntax_Syntax.Tm_uvar
                                                           uu____3104 -> true
                                                       | uu____3121 -> false)))) in
                                   let uu____3122 = solve goal solution in
                                   bind uu____3122
                                     (fun uu____3127  ->
                                        let uu____3128 =
                                          add_implicits implicits1 in
                                        bind uu____3128
                                          (fun uu____3139  ->
                                             let is_free_uvar uv t1 =
                                               let free_uvars =
                                                 let uu____3150 =
                                                   let uu____3157 =
                                                     FStar_Syntax_Free.uvars
                                                       t1 in
                                                   FStar_Util.set_elements
                                                     uu____3157 in
                                                 FStar_List.map
                                                   FStar_Pervasives_Native.fst
                                                   uu____3150 in
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
                                               let uu____3198 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t1 in
                                               match uu____3198 with
                                               | (hd1,uu____3214) ->
                                                   (match hd1.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_uvar
                                                        (uv,uu____3236) ->
                                                        appears uv goals
                                                    | uu____3261 -> false) in
                                             let sub_goals =
                                               FStar_All.pipe_right
                                                 implicits1
                                                 (FStar_List.map
                                                    (fun uu____3303  ->
                                                       match uu____3303 with
                                                       | (_msg,_env,_uvar,term,typ,uu____3321)
                                                           ->
                                                           let uu___115_3322
                                                             = goal in
                                                           let uu____3323 =
                                                             bnorm
                                                               goal.FStar_Tactics_Types.context
                                                               term in
                                                           let uu____3324 =
                                                             bnorm
                                                               goal.FStar_Tactics_Types.context
                                                               typ in
                                                           {
                                                             FStar_Tactics_Types.context
                                                               =
                                                               (uu___115_3322.FStar_Tactics_Types.context);
                                                             FStar_Tactics_Types.witness
                                                               = uu____3323;
                                                             FStar_Tactics_Types.goal_ty
                                                               = uu____3324;
                                                             FStar_Tactics_Types.opts
                                                               =
                                                               (uu___115_3322.FStar_Tactics_Types.opts);
                                                             FStar_Tactics_Types.is_guard
                                                               =
                                                               (uu___115_3322.FStar_Tactics_Types.is_guard)
                                                           })) in
                                             let rec filter' f xs =
                                               match xs with
                                               | [] -> []
                                               | x::xs1 ->
                                                   let uu____3362 = f x xs1 in
                                                   if uu____3362
                                                   then
                                                     let uu____3365 =
                                                       filter' f xs1 in
                                                     x :: uu____3365
                                                   else filter' f xs1 in
                                             let sub_goals1 =
                                               filter'
                                                 (fun g  ->
                                                    fun goals  ->
                                                      let uu____3379 =
                                                        checkone
                                                          g.FStar_Tactics_Types.witness
                                                          goals in
                                                      Prims.op_Negation
                                                        uu____3379) sub_goals in
                                             let uu____3380 =
                                               add_goal_from_guard
                                                 goal.FStar_Tactics_Types.context
                                                 guard
                                                 goal.FStar_Tactics_Types.opts in
                                             bind uu____3380
                                               (fun uu____3385  ->
                                                  let uu____3386 =
                                                    let uu____3389 =
                                                      let uu____3390 =
                                                        let uu____3391 =
                                                          FStar_Syntax_Util.mk_squash
                                                            pre in
                                                        istrivial
                                                          goal.FStar_Tactics_Types.context
                                                          uu____3391 in
                                                      Prims.op_Negation
                                                        uu____3390 in
                                                    if uu____3389
                                                    then
                                                      add_irrelevant_goal
                                                        goal.FStar_Tactics_Types.context
                                                        pre
                                                        goal.FStar_Tactics_Types.opts
                                                    else ret () in
                                                  bind uu____3386
                                                    (fun uu____3396  ->
                                                       add_goals sub_goals1))))))))) in
    focus uu____2500
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3413 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3413 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3423::(e1,uu____3425)::(e2,uu____3427)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3486 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3509 = destruct_eq' typ in
    match uu____3509 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3539 = FStar_Syntax_Util.un_squash typ in
        (match uu____3539 with
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
        let uu____3597 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3597 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3645 = aux e' in
               FStar_Util.map_opt uu____3645
                 (fun uu____3669  ->
                    match uu____3669 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3690 = aux e in
      FStar_Util.map_opt uu____3690
        (fun uu____3714  ->
           match uu____3714 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____3775 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____3775
            (fun uu____3799  ->
               match uu____3799 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___116_3816 = bv in
                     let uu____3817 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___116_3816.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___116_3816.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3817
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___117_3826 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___117_3826.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___117_3826.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3841 = h in
         match uu____3841 with
         | (bv,uu____3845) ->
             let uu____3846 =
               FStar_All.pipe_left mlog
                 (fun uu____3856  ->
                    let uu____3857 = FStar_Syntax_Print.bv_to_string bv in
                    let uu____3858 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3857
                      uu____3858) in
             bind uu____3846
               (fun uu____3861  ->
                  let uu____3862 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____3862 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____3891 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____3891 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____3906 =
                             let uu____3907 = FStar_Syntax_Subst.compress x in
                             uu____3907.FStar_Syntax_Syntax.n in
                           (match uu____3906 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___118_3920 = bv1 in
                                  let uu____3921 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___118_3920.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___118_3920.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____3921
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____3927 =
                                  let uu___119_3928 = goal in
                                  let uu____3929 = push_bvs e0 (bv :: bvs1) in
                                  let uu____3930 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____3931 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____3929;
                                    FStar_Tactics_Types.witness = uu____3930;
                                    FStar_Tactics_Types.goal_ty = uu____3931;
                                    FStar_Tactics_Types.opts =
                                      (uu___119_3928.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___119_3928.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____3927
                            | uu____3932 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____3933 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3960 = b in
           match uu____3960 with
           | (bv,uu____3964) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___120_3968 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___120_3968.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___120_3968.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3972 =
                   let uu____3973 =
                     let uu____3980 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3980) in
                   FStar_Syntax_Syntax.NT uu____3973 in
                 [uu____3972] in
               let uu____3981 = subst_goal bv bv' s1 goal in
               (match uu____3981 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4001 = b in
         match uu____4001 with
         | (bv,uu____4005) ->
             let uu____4006 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4006 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4035 = FStar_Syntax_Util.type_u () in
                  (match uu____4035 with
                   | (ty,u) ->
                       let uu____4044 = new_uvar e0 ty in
                       bind uu____4044
                         (fun t'  ->
                            let bv'' =
                              let uu___121_4054 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_4054.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_4054.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4058 =
                                let uu____4059 =
                                  let uu____4066 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4066) in
                                FStar_Syntax_Syntax.NT uu____4059 in
                              [uu____4058] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___122_4074 = b1 in
                                   let uu____4075 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___122_4074.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___122_4074.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4075
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4081  ->
                                 let uu____4082 =
                                   let uu____4085 =
                                     let uu____4088 =
                                       let uu___123_4089 = goal in
                                       let uu____4090 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4091 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4090;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4091;
                                         FStar_Tactics_Types.opts =
                                           (uu___123_4089.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___123_4089.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4088] in
                                   add_goals uu____4085 in
                                 bind uu____4082
                                   (fun uu____4094  ->
                                      let uu____4095 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal e0 uu____4095
                                        goal.FStar_Tactics_Types.opts))))))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4101 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4101 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4123 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4123 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___124_4157 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___124_4157.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___124_4157.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4169 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4169 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4190 = FStar_Syntax_Print.bv_to_string x in
               let uu____4191 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4190 uu____4191
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4198 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4198 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4220 = FStar_Util.set_mem x fns_ty in
           if uu____4220
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4224 = new_uvar env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4224
                (fun u  ->
                   let uu____4230 =
                     let uu____4231 = trysolve goal u in
                     Prims.op_Negation uu____4231 in
                   if uu____4230
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___125_4236 = goal in
                        let uu____4237 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4237;
                          FStar_Tactics_Types.goal_ty =
                            (uu___125_4236.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___125_4236.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___125_4236.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4239  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4251 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4251 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4275  ->
                    let uu____4276 = clear b in
                    bind uu____4276
                      (fun uu____4280  ->
                         bind intro (fun uu____4282  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___126_4299 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___126_4299.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___126_4299.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___126_4299.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___126_4299.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4301  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___127_4318 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___127_4318.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___127_4318.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___127_4318.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___127_4318.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4320  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4362 = f x in
          bind uu____4362
            (fun y  ->
               let uu____4370 = mapM f xs in
               bind uu____4370 (fun ys  -> ret (y :: ys)))
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
            let uu____4420 = FStar_Syntax_Subst.compress t in
            uu____4420.FStar_Syntax_Syntax.n in
          let uu____4423 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___129_4429 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___129_4429.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___129_4429.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____4423
            (fun t1  ->
               let tn1 =
                 match tn with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____4466 = ff hd1 in
                     bind uu____4466
                       (fun hd2  ->
                          let fa uu____4486 =
                            match uu____4486 with
                            | (a,q) ->
                                let uu____4499 = ff a in
                                bind uu____4499 (fun a1  -> ret (a1, q)) in
                          let uu____4512 = mapM fa args in
                          bind uu____4512
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____4572 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____4572 with
                      | (bs1,t') ->
                          let uu____4581 =
                            let uu____4584 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____4584 t' in
                          bind uu____4581
                            (fun t''  ->
                               let uu____4588 =
                                 let uu____4589 =
                                   let uu____4606 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____4607 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____4606, uu____4607, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____4589 in
                               ret uu____4588))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____4628 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___128_4635 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___128_4635.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___128_4635.FStar_Syntax_Syntax.vars)
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
            let uu____4669 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4669 with
            | (t1,lcomp,g) ->
                let uu____4681 =
                  (let uu____4684 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____4684) ||
                    (let uu____4686 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4686) in
                if uu____4681
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4693 = new_uvar env typ in
                   bind uu____4693
                     (fun ut  ->
                        log ps
                          (fun uu____4704  ->
                             let uu____4705 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4706 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4705 uu____4706);
                        (let uu____4707 =
                           let uu____4710 =
                             let uu____4711 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4711 typ t1 ut in
                           add_irrelevant_goal env uu____4710 opts in
                         bind uu____4707
                           (fun uu____4714  ->
                              let uu____4715 =
                                bind tau
                                  (fun uu____4720  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4715))))
let pointwise:
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____4745 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____4745 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____4782  ->
                     let uu____4783 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____4783);
                bind dismiss_all
                  (fun uu____4786  ->
                     let uu____4787 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____4787
                       (fun gt'  ->
                          log ps
                            (fun uu____4797  ->
                               let uu____4798 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____4798);
                          (let uu____4799 = push_goals gs in
                           bind uu____4799
                             (fun uu____4803  ->
                                add_goals
                                  [(let uu___130_4805 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___130_4805.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___130_4805.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___130_4805.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___130_4805.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4825 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____4825 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4837 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4837 with
            | (hd1,args) ->
                let uu____4870 =
                  let uu____4883 =
                    let uu____4884 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4884.FStar_Syntax_Syntax.n in
                  (uu____4883, args) in
                (match uu____4870 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4898::(l,uu____4900)::(r,uu____4902)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4949 =
                       let uu____4950 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____4950 in
                     if uu____4949
                     then
                       let uu____4953 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____4954 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4953 uu____4954
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____4957) ->
                     let uu____4974 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____4974))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4982 =
         new_uvar g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
       bind uu____4982
         (fun u  ->
            let g' =
              let uu___131_4989 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___131_4989.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___131_4989.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___131_4989.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___131_4989.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____4992  ->
                 let uu____4993 =
                   let uu____4996 =
                     let uu____4997 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4997
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal g.FStar_Tactics_Types.context
                     uu____4996 g.FStar_Tactics_Types.opts in
                 bind uu____4993
                   (fun uu____5000  ->
                      let uu____5001 = add_goals [g'] in
                      bind uu____5001 (fun uu____5005  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___132_5022 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___132_5022.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___132_5022.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___132_5022.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___132_5022.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___132_5022.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___132_5022.FStar_Tactics_Types.__dump)
              })
       | uu____5023 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___133_5038 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___133_5038.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___133_5038.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___133_5038.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___133_5038.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___133_5038.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___133_5038.FStar_Tactics_Types.__dump)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5045 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____5087 =
           (g.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
             g.FStar_Tactics_Types.context t in
         match uu____5087 with
         | (t1,typ,guard) ->
             let uu____5103 = FStar_Syntax_Util.head_and_args typ in
             (match uu____5103 with
              | (hd1,args) ->
                  let uu____5146 =
                    let uu____5159 =
                      let uu____5160 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____5160.FStar_Syntax_Syntax.n in
                    (uu____5159, args) in
                  (match uu____5146 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____5179)::(q,uu____5181)::[]) when
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
                         let uu___134_5219 = g in
                         let uu____5220 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_p in
                         {
                           FStar_Tactics_Types.context = uu____5220;
                           FStar_Tactics_Types.witness =
                             (uu___134_5219.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___134_5219.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___134_5219.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___134_5219.FStar_Tactics_Types.is_guard)
                         } in
                       let g2 =
                         let uu___135_5222 = g in
                         let uu____5223 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_q in
                         {
                           FStar_Tactics_Types.context = uu____5223;
                           FStar_Tactics_Types.witness =
                             (uu___135_5222.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___135_5222.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___135_5222.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___135_5222.FStar_Tactics_Types.is_guard)
                         } in
                       bind dismiss
                         (fun uu____5230  ->
                            let uu____5231 = add_goals [g1; g2] in
                            bind uu____5231
                              (fun uu____5240  ->
                                 let uu____5241 =
                                   let uu____5246 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____5247 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____5246, uu____5247) in
                                 ret uu____5241))
                   | uu____5252 ->
                       let uu____5265 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context typ in
                       fail1 "Not a disjunction: %s" uu____5265)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5288 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5288);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___136_5295 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___136_5295.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___136_5295.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___136_5295.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___136_5295.FStar_Tactics_Types.is_guard)
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
           let uu____5336 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               env tm in
           match uu____5336 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5365 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5371 =
              let uu____5372 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5372 in
            new_uvar env uu____5371 in
      bind uu____5365
        (fun typ  ->
           let uu____5384 = new_uvar env typ in
           bind uu____5384 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5404 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5404)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5424  ->
             let uu____5425 = FStar_Options.unsafe_tactic_exec () in
             if uu____5425
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5431  -> fun uu____5432  -> false) in
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
      let uu____5454 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5454 with
      | (u,uu____5472,g_u) ->
          let g =
            let uu____5487 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5487;
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
      let uu____5504 = goal_of_goal_ty env typ in
      match uu____5504 with
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