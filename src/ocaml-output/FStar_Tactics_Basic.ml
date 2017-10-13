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
let wrap_err: 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____860 = run t ps in
           match uu____860 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____878  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____896 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____910 =
         let uu___126_911 = p in
         let uu____912 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___126_911.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___126_911.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___126_911.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____912;
           FStar_Tactics_Types.smt_goals =
             (uu___126_911.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___126_911.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___126_911.FStar_Tactics_Types.__dump)
         } in
       set uu____910)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____927 = trysolve goal solution in
      if uu____927
      then dismiss
      else
        (let uu____931 =
           let uu____932 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____933 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____934 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____932 uu____933
             uu____934 in
         fail uu____931)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___127_941 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___127_941.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___127_941.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___127_941.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___127_941.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___127_941.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___127_941.FStar_Tactics_Types.__dump)
          }))
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___128_958 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___128_958.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___128_958.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___128_958.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___128_958.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___128_958.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___128_958.FStar_Tactics_Types.__dump)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___129_975 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___129_975.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___129_975.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___129_975.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___129_975.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___129_975.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___129_975.FStar_Tactics_Types.__dump)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___130_992 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___130_992.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___130_992.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___130_992.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___130_992.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___130_992.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___130_992.FStar_Tactics_Types.__dump)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___131_1009 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___131_1009.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___131_1009.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___131_1009.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___131_1009.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___131_1009.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___131_1009.FStar_Tactics_Types.__dump)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1019  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___132_1032 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___132_1032.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___132_1032.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___132_1032.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___132_1032.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___132_1032.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___132_1032.FStar_Tactics_Types.__dump)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1061 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1061 with
        | (u,uu____1077,g_u) ->
            let uu____1091 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1091 (fun uu____1095  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1100 = FStar_Syntax_Util.un_squash t in
    match uu____1100 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1110 =
          let uu____1111 = FStar_Syntax_Subst.compress t' in
          uu____1111.FStar_Syntax_Syntax.n in
        (match uu____1110 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1115 -> false)
    | uu____1116 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1125 = FStar_Syntax_Util.un_squash t in
    match uu____1125 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1135 =
          let uu____1136 = FStar_Syntax_Subst.compress t' in
          uu____1136.FStar_Syntax_Syntax.n in
        (match uu____1135 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1140 -> false)
    | uu____1141 -> false
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
          let uu____1179 = new_uvar reason env typ in
          bind uu____1179
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
             let uu____1237 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1237
           with | e1 -> fail "not typeable")
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1276 =
      bind cur_goal
        (fun goal  ->
           let uu____1282 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1282
             (fun uu____1302  ->
                match uu____1302 with
                | (t1,typ,guard) ->
                    let uu____1314 =
                      let uu____1315 =
                        let uu____1316 =
                          FStar_TypeChecker_Rel.discharge_guard
                            goal.FStar_Tactics_Types.context guard in
                        FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                          uu____1316 in
                      Prims.op_Negation uu____1315 in
                    if uu____1314
                    then fail "got non-trivial guard"
                    else ret typ)) in
    FStar_All.pipe_left (wrap_err "tc") uu____1276
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1344 = mk_irrelevant_goal reason env phi opts in
          bind uu____1344 (fun goal  -> add_goals [goal])
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
       let uu____1366 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1366
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1370 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1370))
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
          let uu____1391 =
            let uu____1392 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1392.FStar_TypeChecker_Env.guard_f in
          match uu____1391 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1396 = istrivial e f in
              if uu____1396
              then ret ()
              else
                (let uu____1400 = mk_irrelevant_goal reason e f opts in
                 bind uu____1400
                   (fun goal  ->
                      let goal1 =
                        let uu___135_1407 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___135_1407.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___135_1407.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___135_1407.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___135_1407.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard = true
                        } in
                      push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1413 = is_irrelevant g in
       if uu____1413
       then bind dismiss (fun uu____1417  -> add_smt_goals [g])
       else
         (let uu____1419 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1419))
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
             let uu____1465 =
               try
                 let uu____1499 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1499
               with | uu____1529 -> fail "divide: not enough goals" in
             bind uu____1465
               (fun uu____1556  ->
                  match uu____1556 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___136_1582 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___136_1582.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___136_1582.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___136_1582.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___136_1582.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___136_1582.FStar_Tactics_Types.__dump)
                        } in
                      let rp =
                        let uu___137_1584 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___137_1584.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___137_1584.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___137_1584.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___137_1584.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___137_1584.FStar_Tactics_Types.__dump)
                        } in
                      let uu____1585 = set lp in
                      bind uu____1585
                        (fun uu____1593  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1607 = set rp in
                                     bind uu____1607
                                       (fun uu____1615  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___138_1631 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___138_1631.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___138_1631.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___138_1631.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___138_1631.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___138_1631.FStar_Tactics_Types.__dump)
                                                      } in
                                                    let uu____1632 = set p' in
                                                    bind uu____1632
                                                      (fun uu____1640  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1660 = divide (Prims.parse_int "1") f idtac in
    bind uu____1660
      (fun uu____1673  -> match uu____1673 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1708::uu____1709 ->
             let uu____1712 =
               let uu____1721 = map tau in
               divide (Prims.parse_int "1") tau uu____1721 in
             bind uu____1712
               (fun uu____1739  ->
                  match uu____1739 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1778 =
        bind t1
          (fun uu____1783  ->
             let uu____1784 = map t2 in
             bind uu____1784 (fun uu____1792  -> ret ())) in
      focus uu____1778
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1803 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1803 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1818 =
             let uu____1819 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1819 in
           if uu____1818
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1825 = new_uvar "intro" env' typ' in
              bind uu____1825
                (fun u  ->
                   let uu____1832 =
                     let uu____1833 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1833 in
                   if uu____1832
                   then
                     let uu____1836 =
                       let uu____1839 =
                         let uu___141_1840 = goal in
                         let uu____1841 = bnorm env' u in
                         let uu____1842 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1841;
                           FStar_Tactics_Types.goal_ty = uu____1842;
                           FStar_Tactics_Types.opts =
                             (uu___141_1840.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___141_1840.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1839 in
                     bind uu____1836 (fun uu____1844  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1850 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1850)
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
       (let uu____1871 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1871 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1890 =
              let uu____1891 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1891 in
            if uu____1890
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1907 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1907; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1909 =
                 let uu____1912 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____1912 in
               bind uu____1909
                 (fun u  ->
                    let lb =
                      let uu____1928 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____1928 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1932 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1932 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____1969 =
                            let uu____1972 =
                              let uu___142_1973 = goal in
                              let uu____1974 = bnorm env' u in
                              let uu____1975 =
                                let uu____1976 = comp_to_typ c in
                                bnorm env' uu____1976 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____1974;
                                FStar_Tactics_Types.goal_ty = uu____1975;
                                FStar_Tactics_Types.opts =
                                  (uu___142_1973.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___142_1973.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____1972 in
                          bind uu____1969
                            (fun uu____1983  ->
                               let uu____1984 =
                                 let uu____1989 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____1989, b) in
                               ret uu____1984)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2003 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2003))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2028 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2028 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___143_2035 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___143_2035.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___143_2035.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___143_2035.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2056 =
          bind get
            (fun ps  ->
               let uu____2062 = __tc e t in
               bind uu____2062
                 (fun uu____2084  ->
                    match uu____2084 with
                    | (t1,uu____2094,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2100 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2100 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2056
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2119 = __tc goal.FStar_Tactics_Types.context t in
         bind uu____2119
           (fun uu____2139  ->
              match uu____2139 with
              | (t1,typ,guard) ->
                  let uu____2151 =
                    let uu____2152 =
                      let uu____2153 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2153 in
                    Prims.op_Negation uu____2152 in
                  if uu____2151
                  then fail "got non-trivial guard"
                  else
                    (let uu____2157 =
                       do_unify goal.FStar_Tactics_Types.context typ
                         goal.FStar_Tactics_Types.goal_ty in
                     if uu____2157
                     then solve goal t1
                     else
                       (let uu____2161 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context t1 in
                        let uu____2162 =
                          let uu____2163 =
                            bnorm goal.FStar_Tactics_Types.context typ in
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context uu____2163 in
                        let uu____2164 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context
                            goal.FStar_Tactics_Types.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2161 uu____2162 uu____2164))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2173 =
      mlog
        (fun uu____2178  ->
           let uu____2179 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact: tm = %s\n" uu____2179)
        (fun uu____2182  -> let uu____2183 = __exact tm in focus uu____2183) in
    FStar_All.pipe_left (wrap_err "exact") uu____2173
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2202 =
             let uu____2209 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2209 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2202 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2236 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2256 =
               let uu____2261 = __exact tm in trytac uu____2261 in
             bind uu____2256
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2274 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2274 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2306  ->
                                let uu____2307 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2307)
                             (fun uu____2310  ->
                                let uu____2311 =
                                  let uu____2312 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2312 in
                                if uu____2311
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2316 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2316
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2336 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2336 in
                                        let uu____2337 =
                                          __apply uopt tm' typ' in
                                        bind uu____2337
                                          (fun uu____2345  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2347 =
                                               let uu____2348 =
                                                 let uu____2351 =
                                                   let uu____2352 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2352 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2351 in
                                               uu____2348.FStar_Syntax_Syntax.n in
                                             match uu____2347 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2380) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2408 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2408
                                                      then ret ()
                                                      else
                                                        (let uu____2412 =
                                                           let uu____2415 =
                                                             let uu___144_2416
                                                               = goal in
                                                             let uu____2417 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2418 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___144_2416.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2417;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2418;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___144_2416.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2415] in
                                                         add_goals uu____2412))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2469 =
        mlog
          (fun uu____2474  ->
             let uu____2475 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2475)
          (fun uu____2477  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2481 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2481
                    (fun uu____2502  ->
                       match uu____2502 with
                       | (tm1,typ,guard) ->
                           let uu____2514 =
                             let uu____2517 =
                               let uu____2520 = __apply uopt tm1 typ in
                               bind uu____2520
                                 (fun uu____2524  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2517 in
                           let uu____2525 =
                             let uu____2528 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context tm1 in
                             let uu____2529 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context typ in
                             let uu____2530 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2528 uu____2529 uu____2530 in
                           try_unif uu____2514 uu____2525))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2469
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2543 =
      let uu____2546 =
        mlog
          (fun uu____2551  ->
             let uu____2552 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2552)
          (fun uu____2555  ->
             let is_unit_t t =
               let uu____2560 =
                 let uu____2561 = FStar_Syntax_Subst.compress t in
                 uu____2561.FStar_Syntax_Syntax.n in
               match uu____2560 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____2565 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____2569 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2569
                    (fun uu____2591  ->
                       match uu____2591 with
                       | (tm1,t,guard) ->
                           let uu____2603 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____2603 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____2633 =
                                     FStar_List.fold_left
                                       (fun uu____2679  ->
                                          fun uu____2680  ->
                                            match (uu____2679, uu____2680)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____2783 =
                                                  is_unit_t b_t in
                                                if uu____2783
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____2821 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____2821 with
                                                   | (u,uu____2851,g_u) ->
                                                       let uu____2865 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____2865,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____2633 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____2935 =
                                         let uu____2944 =
                                           let uu____2953 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____2953.FStar_Syntax_Syntax.effect_args in
                                         match uu____2944 with
                                         | pre::post::uu____2964 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3005 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____2935 with
                                        | (pre,post) ->
                                            let uu____3034 =
                                              let uu____3035 =
                                                let uu____3036 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3036
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3035 in
                                            if uu____3034
                                            then
                                              let uu____3039 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3040 =
                                                let uu____3041 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post in
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3041 in
                                              let uu____3042 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3039 uu____3040
                                                uu____3042
                                            else
                                              (let solution =
                                                 let uu____3045 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3045 in
                                               let uu____3046 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3046
                                                 (fun uu____3052  ->
                                                    let implicits1 =
                                                      FStar_All.pipe_right
                                                        implicits.FStar_TypeChecker_Env.implicits
                                                        (FStar_List.filter
                                                           (fun uu____3120 
                                                              ->
                                                              match uu____3120
                                                              with
                                                              | (uu____3133,uu____3134,uu____3135,tm2,uu____3137,uu____3138)
                                                                  ->
                                                                  let uu____3139
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    tm2 in
                                                                  (match uu____3139
                                                                   with
                                                                   | 
                                                                   (hd1,uu____3155)
                                                                    ->
                                                                    let uu____3176
                                                                    =
                                                                    let uu____3177
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3177.FStar_Syntax_Syntax.n in
                                                                    (match uu____3176
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3180
                                                                    -> true
                                                                    | 
                                                                    uu____3197
                                                                    -> false)))) in
                                                    let uu____3198 =
                                                      solve goal solution in
                                                    bind uu____3198
                                                      (fun uu____3209  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3220 =
                                                               let uu____3227
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3227 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3220 in
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
                                                           let uu____3268 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3268
                                                           with
                                                           | (hd1,uu____3284)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3306)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3331
                                                                    -> false) in
                                                         let sub_goals =
                                                           FStar_All.pipe_right
                                                             implicits1
                                                             (FStar_List.map
                                                                (fun
                                                                   uu____3373
                                                                    ->
                                                                   match uu____3373
                                                                   with
                                                                   | 
                                                                   (_msg,_env,_uvar,term,typ,uu____3391)
                                                                    ->
                                                                    let uu___147_3392
                                                                    = goal in
                                                                    let uu____3393
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3394
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___147_3392.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3393;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3394;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___147_3392.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___147_3392.FStar_Tactics_Types.is_guard)
                                                                    })) in
                                                         let rec filter' f xs
                                                           =
                                                           match xs with
                                                           | [] -> []
                                                           | x::xs1 ->
                                                               let uu____3432
                                                                 = f x xs1 in
                                                               if uu____3432
                                                               then
                                                                 let uu____3435
                                                                   =
                                                                   filter' f
                                                                    xs1 in
                                                                 x ::
                                                                   uu____3435
                                                               else
                                                                 filter' f
                                                                   xs1 in
                                                         let sub_goals1 =
                                                           filter'
                                                             (fun g  ->
                                                                fun goals  ->
                                                                  let uu____3449
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                  Prims.op_Negation
                                                                    uu____3449)
                                                             sub_goals in
                                                         let uu____3450 =
                                                           add_goal_from_guard
                                                             "apply_lemma guard"
                                                             goal.FStar_Tactics_Types.context
                                                             guard
                                                             goal.FStar_Tactics_Types.opts in
                                                         bind uu____3450
                                                           (fun uu____3455 
                                                              ->
                                                              let uu____3456
                                                                =
                                                                let uu____3459
                                                                  =
                                                                  let uu____3460
                                                                    =
                                                                    let uu____3461
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____3461 in
                                                                  Prims.op_Negation
                                                                    uu____3460 in
                                                                if uu____3459
                                                                then
                                                                  add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                else ret () in
                                                              bind uu____3456
                                                                (fun
                                                                   uu____3466
                                                                    ->
                                                                   add_goals
                                                                    sub_goals1))))))))))) in
      focus uu____2546 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2543
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3487 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3487 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3497::(e1,uu____3499)::(e2,uu____3501)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3560 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3583 = destruct_eq' typ in
    match uu____3583 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3613 = FStar_Syntax_Util.un_squash typ in
        (match uu____3613 with
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
        let uu____3671 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3671 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3719 = aux e' in
               FStar_Util.map_opt uu____3719
                 (fun uu____3743  ->
                    match uu____3743 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3764 = aux e in
      FStar_Util.map_opt uu____3764
        (fun uu____3788  ->
           match uu____3788 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____3849 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____3849
            (fun uu____3873  ->
               match uu____3873 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___148_3890 = bv in
                     let uu____3891 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___148_3890.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___148_3890.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3891
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___149_3900 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___149_3900.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___149_3900.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3914 = h in
         match uu____3914 with
         | (bv,uu____3918) ->
             mlog
               (fun uu____3922  ->
                  let uu____3923 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____3924 =
                    FStar_Syntax_Print.term_to_string
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3923
                    uu____3924)
               (fun uu____3927  ->
                  let uu____3928 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____3928 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____3957 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____3957 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____3972 =
                             let uu____3973 = FStar_Syntax_Subst.compress x in
                             uu____3973.FStar_Syntax_Syntax.n in
                           (match uu____3972 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___150_3986 = bv1 in
                                  let uu____3987 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___150_3986.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___150_3986.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____3987
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____3993 =
                                  let uu___151_3994 = goal in
                                  let uu____3995 = push_bvs e0 (bv :: bvs1) in
                                  let uu____3996 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____3997 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____3995;
                                    FStar_Tactics_Types.witness = uu____3996;
                                    FStar_Tactics_Types.goal_ty = uu____3997;
                                    FStar_Tactics_Types.opts =
                                      (uu___151_3994.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___151_3994.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____3993
                            | uu____3998 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____3999 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4026 = b in
           match uu____4026 with
           | (bv,uu____4030) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___152_4034 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___152_4034.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___152_4034.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4038 =
                   let uu____4039 =
                     let uu____4046 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4046) in
                   FStar_Syntax_Syntax.NT uu____4039 in
                 [uu____4038] in
               let uu____4047 = subst_goal bv bv' s1 goal in
               (match uu____4047 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4067 = b in
         match uu____4067 with
         | (bv,uu____4071) ->
             let uu____4072 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4072 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4101 = FStar_Syntax_Util.type_u () in
                  (match uu____4101 with
                   | (ty,u) ->
                       let uu____4110 = new_uvar "binder_retype" e0 ty in
                       bind uu____4110
                         (fun t'  ->
                            let bv'' =
                              let uu___153_4120 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___153_4120.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___153_4120.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4124 =
                                let uu____4125 =
                                  let uu____4132 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4132) in
                                FStar_Syntax_Syntax.NT uu____4125 in
                              [uu____4124] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___154_4140 = b1 in
                                   let uu____4141 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___154_4140.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___154_4140.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4141
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4147  ->
                                 let uu____4148 =
                                   let uu____4151 =
                                     let uu____4154 =
                                       let uu___155_4155 = goal in
                                       let uu____4156 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4157 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4156;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4157;
                                         FStar_Tactics_Types.opts =
                                           (uu___155_4155.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___155_4155.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4154] in
                                   add_goals uu____4151 in
                                 bind uu____4148
                                   (fun uu____4160  ->
                                      let uu____4161 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4161
                                        goal.FStar_Tactics_Types.opts))))))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4167 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4167 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4189 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4189 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___156_4223 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___156_4223.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___156_4223.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4235 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4235 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4256 = FStar_Syntax_Print.bv_to_string x in
               let uu____4257 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4256 uu____4257
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4264 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4264 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4286 = FStar_Util.set_mem x fns_ty in
           if uu____4286
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4290 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4290
                (fun u  ->
                   let uu____4296 =
                     let uu____4297 = trysolve goal u in
                     Prims.op_Negation uu____4297 in
                   if uu____4296
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___157_4302 = goal in
                        let uu____4303 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4303;
                          FStar_Tactics_Types.goal_ty =
                            (uu___157_4302.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___157_4302.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___157_4302.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4305  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4317 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4317 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4341  ->
                    let uu____4342 = clear b in
                    bind uu____4342
                      (fun uu____4346  ->
                         bind intro (fun uu____4348  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___158_4365 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___158_4365.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___158_4365.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___158_4365.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___158_4365.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4367  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___159_4384 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___159_4384.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___159_4384.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___159_4384.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___159_4384.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4386  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4428 = f x in
          bind uu____4428
            (fun y  ->
               let uu____4436 = mapM f xs in
               bind uu____4436 (fun ys  -> ret (y :: ys)))
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
            let uu____4486 = FStar_Syntax_Subst.compress t in
            uu____4486.FStar_Syntax_Syntax.n in
          let uu____4489 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___161_4495 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___161_4495.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___161_4495.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____4489
            (fun t1  ->
               let tn1 =
                 match tn with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____4532 = ff hd1 in
                     bind uu____4532
                       (fun hd2  ->
                          let fa uu____4552 =
                            match uu____4552 with
                            | (a,q) ->
                                let uu____4565 = ff a in
                                bind uu____4565 (fun a1  -> ret (a1, q)) in
                          let uu____4578 = mapM fa args in
                          bind uu____4578
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____4638 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____4638 with
                      | (bs1,t') ->
                          let uu____4647 =
                            let uu____4650 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____4650 t' in
                          bind uu____4647
                            (fun t''  ->
                               let uu____4654 =
                                 let uu____4655 =
                                   let uu____4672 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____4673 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____4672, uu____4673, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____4655 in
                               ret uu____4654))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____4694 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___160_4701 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___160_4701.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___160_4701.FStar_Syntax_Syntax.vars)
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
            let uu____4735 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4735 with
            | (t1,lcomp,g) ->
                let uu____4747 =
                  (let uu____4750 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____4750) ||
                    (let uu____4752 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4752) in
                if uu____4747
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4759 = new_uvar "pointwise_rec" env typ in
                   bind uu____4759
                     (fun ut  ->
                        log ps
                          (fun uu____4770  ->
                             let uu____4771 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4772 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4771 uu____4772);
                        (let uu____4773 =
                           let uu____4776 =
                             let uu____4777 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4777 typ t1 ut in
                           add_irrelevant_goal "pointwise_rec equation" env
                             uu____4776 opts in
                         bind uu____4773
                           (fun uu____4780  ->
                              let uu____4781 =
                                bind tau
                                  (fun uu____4786  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4781))))
let pointwise:
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____4811 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____4811 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____4848  ->
                     let uu____4849 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____4849);
                bind dismiss_all
                  (fun uu____4852  ->
                     let uu____4853 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____4853
                       (fun gt'  ->
                          log ps
                            (fun uu____4863  ->
                               let uu____4864 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____4864);
                          (let uu____4865 = push_goals gs in
                           bind uu____4865
                             (fun uu____4869  ->
                                add_goals
                                  [(let uu___162_4871 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___162_4871.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___162_4871.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___162_4871.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___162_4871.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4891 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____4891 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4903 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4903 with
            | (hd1,args) ->
                let uu____4936 =
                  let uu____4949 =
                    let uu____4950 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4950.FStar_Syntax_Syntax.n in
                  (uu____4949, args) in
                (match uu____4936 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4964::(l,uu____4966)::(r,uu____4968)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5015 =
                       let uu____5016 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5016 in
                     if uu____5015
                     then
                       let uu____5019 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____5020 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5019 uu____5020
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5023) ->
                     let uu____5040 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5040))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5048 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5048
         (fun u  ->
            let g' =
              let uu___163_5055 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___163_5055.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___163_5055.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___163_5055.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___163_5055.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5058  ->
                 let uu____5059 =
                   let uu____5062 =
                     let uu____5063 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5063
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5062
                     g.FStar_Tactics_Types.opts in
                 bind uu____5059
                   (fun uu____5066  ->
                      let uu____5067 = add_goals [g'] in
                      bind uu____5067 (fun uu____5071  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___164_5088 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___164_5088.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___164_5088.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___164_5088.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___164_5088.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___164_5088.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___164_5088.FStar_Tactics_Types.__dump)
              })
       | uu____5089 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___165_5104 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___165_5104.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___165_5104.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___165_5104.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___165_5104.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___165_5104.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___165_5104.FStar_Tactics_Types.__dump)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5111 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5130 =
      bind cur_goal
        (fun g  ->
           let uu____5144 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5144
             (fun uu____5180  ->
                match uu____5180 with
                | (t1,typ,guard) ->
                    let uu____5196 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5196 with
                     | (hd1,args) ->
                         let uu____5239 =
                           let uu____5252 =
                             let uu____5253 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5253.FStar_Syntax_Syntax.n in
                           (uu____5252, args) in
                         (match uu____5239 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5272)::(q,uu____5274)::[]) when
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
                                let uu___166_5312 = g in
                                let uu____5313 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5313;
                                  FStar_Tactics_Types.witness =
                                    (uu___166_5312.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___166_5312.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___166_5312.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___166_5312.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___167_5315 = g in
                                let uu____5316 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5316;
                                  FStar_Tactics_Types.witness =
                                    (uu___167_5315.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___167_5315.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___167_5315.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___167_5315.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5323  ->
                                   let uu____5324 = add_goals [g1; g2] in
                                   bind uu____5324
                                     (fun uu____5333  ->
                                        let uu____5334 =
                                          let uu____5339 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5340 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5339, uu____5340) in
                                        ret uu____5334))
                          | uu____5345 ->
                              let uu____5358 =
                                FStar_TypeChecker_Normalize.term_to_string
                                  g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5358)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5130
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5397 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5397);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___168_5404 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___168_5404.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___168_5404.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___168_5404.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___168_5404.FStar_Tactics_Types.is_guard)
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
      let uu____5442 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____5450 = __tc env tm in
             bind uu____5450
               (fun uu____5470  ->
                  match uu____5470 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____5442
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5503 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5509 =
              let uu____5510 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5510 in
            new_uvar "uvar_env.2" env uu____5509 in
      bind uu____5503
        (fun typ  ->
           let uu____5522 = new_uvar "uvar_env" env typ in
           bind uu____5522 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____5535 =
      bind cur_goal
        (fun goal  ->
           let uu____5541 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____5541
             (fun uu____5561  ->
                match uu____5561 with
                | (t1,typ,guard) ->
                    let uu____5573 =
                      let uu____5574 =
                        let uu____5575 =
                          FStar_TypeChecker_Rel.discharge_guard
                            goal.FStar_Tactics_Types.context guard in
                        FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                          uu____5575 in
                      Prims.op_Negation uu____5574 in
                    if uu____5573
                    then fail "got non-trivial guard"
                    else
                      (let uu____5579 =
                         let uu____5582 =
                           let uu___169_5583 = goal in
                           let uu____5584 =
                             bnorm goal.FStar_Tactics_Types.context t1 in
                           let uu____5585 =
                             bnorm goal.FStar_Tactics_Types.context typ in
                           {
                             FStar_Tactics_Types.context =
                               (uu___169_5583.FStar_Tactics_Types.context);
                             FStar_Tactics_Types.witness = uu____5584;
                             FStar_Tactics_Types.goal_ty = uu____5585;
                             FStar_Tactics_Types.opts =
                               (uu___169_5583.FStar_Tactics_Types.opts);
                             FStar_Tactics_Types.is_guard = false
                           } in
                         [uu____5582] in
                       add_goals uu____5579))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____5535
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5605 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5605)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5625  ->
             let uu____5626 = FStar_Options.unsafe_tactic_exec () in
             if uu____5626
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5632  -> fun uu____5633  -> false) in
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
      let uu____5655 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5655 with
      | (u,uu____5673,g_u) ->
          let g =
            let uu____5688 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5688;
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
      let uu____5705 = goal_of_goal_ty env typ in
      match uu____5705 with
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