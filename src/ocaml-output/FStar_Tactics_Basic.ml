
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
let decr_depth:
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.proofstate =
  fun ps  ->
    let uu___88_120 = ps in
    {
      FStar_Tactics_Types.main_context =
        (uu___88_120.FStar_Tactics_Types.main_context);
      FStar_Tactics_Types.main_goal =
        (uu___88_120.FStar_Tactics_Types.main_goal);
      FStar_Tactics_Types.all_implicits =
        (uu___88_120.FStar_Tactics_Types.all_implicits);
      FStar_Tactics_Types.goals = (uu___88_120.FStar_Tactics_Types.goals);
      FStar_Tactics_Types.smt_goals =
        (uu___88_120.FStar_Tactics_Types.smt_goals);
      FStar_Tactics_Types.depth =
        (ps.FStar_Tactics_Types.depth - (Prims.parse_int "1"))
    }
let incr_depth:
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.proofstate =
  fun ps  ->
    let uu___89_125 = ps in
    {
      FStar_Tactics_Types.main_context =
        (uu___89_125.FStar_Tactics_Types.main_context);
      FStar_Tactics_Types.main_goal =
        (uu___89_125.FStar_Tactics_Types.main_goal);
      FStar_Tactics_Types.all_implicits =
        (uu___89_125.FStar_Tactics_Types.all_implicits);
      FStar_Tactics_Types.goals = (uu___89_125.FStar_Tactics_Types.goals);
      FStar_Tactics_Types.smt_goals =
        (uu___89_125.FStar_Tactics_Types.smt_goals);
      FStar_Tactics_Types.depth =
        (ps.FStar_Tactics_Types.depth + (Prims.parse_int "1"))
    }
let bind: 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____165 = run t1 p in
           match uu____165 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____172 = t2 a in run uu____172 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: FStar_Tactics_Types.goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____184 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____184
        (FStar_Syntax_Print.binders_to_string ", ") in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
    let uu____187 =
      FStar_TypeChecker_Normalize.term_to_string
        g.FStar_Tactics_Types.context w in
    let uu____188 =
      FStar_TypeChecker_Normalize.term_to_string
        g.FStar_Tactics_Types.context t in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____187 uu____188
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____201 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____201
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____214 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____214
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____231 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____231
let comp_to_typ: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____237) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____247) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: FStar_Tactics_Types.goal -> Prims.bool =
  fun g  ->
    let uu____261 =
      let uu____266 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty in
      FStar_Syntax_Util.un_squash uu____266 in
    match uu____261 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____272 -> false
let dump_goal:
  'Auu____283 . 'Auu____283 -> FStar_Tactics_Types.goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____293 = goal_to_string goal in tacprint uu____293
let dump_cur: FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____303 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____307 = FStar_List.hd ps.FStar_Tactics_Types.goals in
            dump_goal ps uu____307))
let ps_to_string:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu____315  ->
    match uu____315 with
    | (msg,ps) ->
        let uu____322 = FStar_Util.string_of_int ps.FStar_Tactics_Types.depth in
        let uu____323 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.goals) in
        let uu____324 =
          let uu____325 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.goals in
          FStar_String.concat "\n" uu____325 in
        let uu____328 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.smt_goals) in
        let uu____329 =
          let uu____330 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.smt_goals in
          FStar_String.concat "\n" uu____330 in
        FStar_Util.format6
          "State dump @ depth %s(%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s"
          uu____322 msg uu____323 uu____324 uu____328 uu____329
let goal_to_json: FStar_Tactics_Types.goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____338 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____338 FStar_Syntax_Print.binders_to_json in
    let uu____339 =
      let uu____346 =
        let uu____353 =
          let uu____358 =
            let uu____359 =
              let uu____366 =
                let uu____371 =
                  let uu____372 =
                    FStar_TypeChecker_Normalize.term_to_string
                      g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness in
                  FStar_Util.JsonStr uu____372 in
                ("witness", uu____371) in
              let uu____373 =
                let uu____380 =
                  let uu____385 =
                    let uu____386 =
                      FStar_TypeChecker_Normalize.term_to_string
                        g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty in
                    FStar_Util.JsonStr uu____386 in
                  ("type", uu____385) in
                [uu____380] in
              uu____366 :: uu____373 in
            FStar_Util.JsonAssoc uu____359 in
          ("goal", uu____358) in
        [uu____353] in
      ("hyps", g_binders) :: uu____346 in
    FStar_Util.JsonAssoc uu____339
let ps_to_json:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____418  ->
    match uu____418 with
    | (msg,ps) ->
        let uu____425 =
          let uu____432 =
            let uu____439 =
              let uu____444 =
                let uu____445 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals in
                FStar_Util.JsonList uu____445 in
              ("goals", uu____444) in
            let uu____448 =
              let uu____455 =
                let uu____460 =
                  let uu____461 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals in
                  FStar_Util.JsonList uu____461 in
                ("smt-goals", uu____460) in
              [uu____455] in
            uu____439 :: uu____448 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____432 in
        FStar_Util.JsonAssoc uu____425
let dump_proofstate:
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____490  ->
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
let tracepoint: FStar_Tactics_Types.proofstate -> Prims.unit =
  fun ps  ->
    let uu____524 =
      (FStar_Options.tactic_trace ()) ||
        (let uu____526 = FStar_Options.tactic_trace_d () in
         ps.FStar_Tactics_Types.depth <= uu____526) in
    if uu____524 then dump_proofstate ps "TRACE" else ()
let get: FStar_Tactics_Types.proofstate tac =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p))
let tac_verb_dbg: Prims.bool FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let rec log:
  FStar_Tactics_Types.proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit
  =
  fun ps  ->
    fun f  ->
      let uu____558 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____558 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____612 =
              let uu____615 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____615 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____612);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
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
         let uu___92_862 = p in
         let uu____863 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___92_862.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___92_862.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___92_862.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____863;
           FStar_Tactics_Types.smt_goals =
             (uu___92_862.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___92_862.FStar_Tactics_Types.depth)
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
         (let uu___93_892 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___93_892.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___93_892.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___93_892.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___93_892.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___93_892.FStar_Tactics_Types.depth)
          }))
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___94_909 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___94_909.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___94_909.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___94_909.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___94_909.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___94_909.FStar_Tactics_Types.depth)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___95_926 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___95_926.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___95_926.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___95_926.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___95_926.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___95_926.FStar_Tactics_Types.depth)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___96_943 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___96_943.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___96_943.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___96_943.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___96_943.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___96_943.FStar_Tactics_Types.depth)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___97_960 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___97_960.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___97_960.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___97_960.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___97_960.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___97_960.FStar_Tactics_Types.depth)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____970  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___98_983 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___98_983.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___98_983.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___98_983.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___98_983.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___98_983.FStar_Tactics_Types.depth)
            }))
let new_uvar: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun typ  ->
      let uu____1008 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____1008 with
      | (u,uu____1024,g_u) ->
          let uu____1038 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____1038 (fun uu____1042  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1047 = FStar_Syntax_Util.un_squash t in
    match uu____1047 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1057 =
          let uu____1058 = FStar_Syntax_Subst.compress t' in
          uu____1058.FStar_Syntax_Syntax.n in
        (match uu____1057 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1062 -> false)
    | uu____1063 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1072 = FStar_Syntax_Util.un_squash t in
    match uu____1072 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1082 =
          let uu____1083 = FStar_Syntax_Subst.compress t' in
          uu____1083.FStar_Syntax_Syntax.n in
        (match uu____1082 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1087 -> false)
    | uu____1088 -> false
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
        let uu____1122 = new_uvar env typ in
        bind uu____1122
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
        let uu____1145 = mk_irrelevant_goal env phi opts in
        bind uu____1145 (fun goal  -> add_goals [goal])
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
       let uu____1167 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1167
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1171 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1171))
let add_goal_from_guard:
  env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Options.optionstate -> Prims.unit tac
  =
  fun e  ->
    fun g  ->
      fun opts  ->
        let uu____1188 =
          let uu____1189 = FStar_TypeChecker_Rel.simplify_guard e g in
          uu____1189.FStar_TypeChecker_Env.guard_f in
        match uu____1188 with
        | FStar_TypeChecker_Common.Trivial  -> ret ()
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____1193 = istrivial e f in
            if uu____1193
            then ret ()
            else
              (let uu____1197 = mk_irrelevant_goal e f opts in
               bind uu____1197
                 (fun goal  ->
                    let goal1 =
                      let uu___99_1204 = goal in
                      {
                        FStar_Tactics_Types.context =
                          (uu___99_1204.FStar_Tactics_Types.context);
                        FStar_Tactics_Types.witness =
                          (uu___99_1204.FStar_Tactics_Types.witness);
                        FStar_Tactics_Types.goal_ty =
                          (uu___99_1204.FStar_Tactics_Types.goal_ty);
                        FStar_Tactics_Types.opts =
                          (uu___99_1204.FStar_Tactics_Types.opts);
                        FStar_Tactics_Types.is_guard = true
                      } in
                    push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1210 = is_irrelevant g in
       if uu____1210
       then bind dismiss (fun uu____1214  -> add_smt_goals [g])
       else
         (let uu____1216 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1216))
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
             let uu____1262 =
               try
                 let uu____1296 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1296
               with | uu____1326 -> fail "divide: not enough goals" in
             bind uu____1262
               (fun uu____1353  ->
                  match uu____1353 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___100_1379 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___100_1379.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___100_1379.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___100_1379.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___100_1379.FStar_Tactics_Types.depth)
                        } in
                      let rp =
                        let uu___101_1381 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___101_1381.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___101_1381.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___101_1381.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___101_1381.FStar_Tactics_Types.depth)
                        } in
                      let uu____1382 = set lp in
                      bind uu____1382
                        (fun uu____1390  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1404 = set rp in
                                     bind uu____1404
                                       (fun uu____1412  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___102_1428 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___102_1428.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___102_1428.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___102_1428.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___102_1428.FStar_Tactics_Types.depth)
                                                      } in
                                                    let uu____1429 = set p' in
                                                    bind uu____1429
                                                      (fun uu____1437  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1457 = divide (Prims.parse_int "1") f idtac in
    bind uu____1457
      (fun uu____1470  -> match uu____1470 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1505::uu____1506 ->
             let uu____1509 =
               let uu____1518 = map tau in
               divide (Prims.parse_int "1") tau uu____1518 in
             bind uu____1509
               (fun uu____1536  ->
                  match uu____1536 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1575 =
        bind t1
          (fun uu____1580  ->
             let uu____1581 = map t2 in
             bind uu____1581 (fun uu____1589  -> ret ())) in
      focus uu____1575
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1600 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1600 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1615 =
             let uu____1616 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1616 in
           if uu____1615
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1622 = new_uvar env' typ' in
              bind uu____1622
                (fun u  ->
                   let uu____1629 =
                     let uu____1630 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1630 in
                   if uu____1629
                   then
                     let uu____1633 =
                       let uu____1636 =
                         let uu___105_1637 = goal in
                         let uu____1638 = bnorm env' u in
                         let uu____1639 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1638;
                           FStar_Tactics_Types.goal_ty = uu____1639;
                           FStar_Tactics_Types.opts =
                             (uu___105_1637.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___105_1637.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1636 in
                     bind uu____1633 (fun uu____1641  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1647 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1647)
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
       (let uu____1668 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1668 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1687 =
              let uu____1688 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1688 in
            if uu____1687
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1704 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1704; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1706 =
                 let uu____1709 = comp_to_typ c in new_uvar env' uu____1709 in
               bind uu____1706
                 (fun u  ->
                    let lb =
                      let uu____1725 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____1725 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1729 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1729 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____1766 =
                            let uu____1769 =
                              let uu___106_1770 = goal in
                              let uu____1771 = bnorm env' u in
                              let uu____1772 =
                                let uu____1773 = comp_to_typ c in
                                bnorm env' uu____1773 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____1771;
                                FStar_Tactics_Types.goal_ty = uu____1772;
                                FStar_Tactics_Types.opts =
                                  (uu___106_1770.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___106_1770.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____1769 in
                          bind uu____1766
                            (fun uu____1780  ->
                               let uu____1781 =
                                 let uu____1786 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____1786, b) in
                               ret uu____1781)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____1800 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1800))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____1825 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1825 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___107_1832 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___107_1832.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___107_1832.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___107_1832.FStar_Tactics_Types.is_guard)
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
             let uu____1856 = FStar_TypeChecker_Normalize.tr_norm_steps s in
             FStar_List.append
               [FStar_TypeChecker_Normalize.Reify;
               FStar_TypeChecker_Normalize.UnfoldTac] uu____1856 in
           let t1 = normalize steps ps.FStar_Tactics_Types.main_context t in
           ret t1)
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1871 =
           try
             let uu____1899 =
               (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
                 goal.FStar_Tactics_Types.context t in
             ret uu____1899
           with
           | e ->
               let uu____1926 = FStar_Syntax_Print.term_to_string t in
               let uu____1927 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1926
                 uu____1927 in
         bind uu____1871
           (fun uu____1945  ->
              match uu____1945 with
              | (t1,typ,guard) ->
                  let uu____1957 =
                    let uu____1958 =
                      let uu____1959 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1959 in
                    Prims.op_Negation uu____1958 in
                  if uu____1957
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1963 =
                       do_unify goal.FStar_Tactics_Types.context typ
                         goal.FStar_Tactics_Types.goal_ty in
                     if uu____1963
                     then solve goal t1
                     else
                       (let uu____1967 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context t1 in
                        let uu____1968 =
                          let uu____1969 =
                            bnorm goal.FStar_Tactics_Types.context typ in
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context uu____1969 in
                        let uu____1970 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context
                            goal.FStar_Tactics_Types.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1967 uu____1968 uu____1970))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  -> let uu____1979 = __exact t in focus uu____1979
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1993 =
           try
             let uu____2021 =
               FStar_TypeChecker_TcTerm.tc_term
                 goal.FStar_Tactics_Types.context t in
             ret uu____2021
           with
           | e ->
               let uu____2048 = FStar_Syntax_Print.term_to_string t in
               let uu____2049 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2048
                 uu____2049 in
         bind uu____1993
           (fun uu____2067  ->
              match uu____2067 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2085 =
                       let uu____2086 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2086 in
                     if uu____2085
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2090 =
                          let uu____2099 =
                            let uu____2108 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2108.FStar_Syntax_Syntax.effect_args in
                          match uu____2099 with
                          | pre::post::uu____2119 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2160 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2090 with
                        | (pre,post) ->
                            let uu____2189 =
                              do_unify goal.FStar_Tactics_Types.context post
                                goal.FStar_Tactics_Types.goal_ty in
                            if uu____2189
                            then
                              let uu____2192 = solve goal t1 in
                              bind uu____2192
                                (fun uu____2196  ->
                                   add_irrelevant_goal
                                     goal.FStar_Tactics_Types.context pre
                                     goal.FStar_Tactics_Types.opts)
                            else
                              (let uu____2198 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context t1 in
                               let uu____2199 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context post in
                               let uu____2200 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2198 uu____2199 uu____2200)))))
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2213 =
             let uu____2220 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2220 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2213 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2247 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2267 =
               let uu____2272 = __exact tm in trytac uu____2272 in
             bind uu____2267
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2285 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2285 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           let uu____2315 =
                             let uu____2316 =
                               FStar_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu____2316 in
                           if uu____2315
                           then fail "apply: not total codomain"
                           else
                             (let uu____2320 =
                                new_uvar goal.FStar_Tactics_Types.context
                                  bv.FStar_Syntax_Syntax.sort in
                              bind uu____2320
                                (fun u  ->
                                   let tm' =
                                     FStar_Syntax_Syntax.mk_Tm_app tm
                                       [(u, aq)] FStar_Pervasives_Native.None
                                       (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                   let typ' =
                                     let uu____2340 = comp_to_typ c in
                                     FStar_All.pipe_left
                                       (FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.NT (bv, u)])
                                       uu____2340 in
                                   let uu____2341 = __apply uopt tm' typ' in
                                   bind uu____2341
                                     (fun uu____2349  ->
                                        let u1 =
                                          bnorm
                                            goal.FStar_Tactics_Types.context
                                            u in
                                        let uu____2351 =
                                          let uu____2352 =
                                            let uu____2355 =
                                              let uu____2356 =
                                                FStar_Syntax_Util.head_and_args
                                                  u1 in
                                              FStar_Pervasives_Native.fst
                                                uu____2356 in
                                            FStar_Syntax_Subst.compress
                                              uu____2355 in
                                          uu____2352.FStar_Syntax_Syntax.n in
                                        match uu____2351 with
                                        | FStar_Syntax_Syntax.Tm_uvar
                                            (uvar,uu____2384) ->
                                            bind get
                                              (fun ps  ->
                                                 let uu____2412 =
                                                   uopt &&
                                                     (uvar_free uvar ps) in
                                                 if uu____2412
                                                 then ret ()
                                                 else
                                                   (let uu____2416 =
                                                      let uu____2419 =
                                                        let uu___112_2420 =
                                                          goal in
                                                        let uu____2421 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            u1 in
                                                        let uu____2422 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          FStar_Tactics_Types.context
                                                            =
                                                            (uu___112_2420.FStar_Tactics_Types.context);
                                                          FStar_Tactics_Types.witness
                                                            = uu____2421;
                                                          FStar_Tactics_Types.goal_ty
                                                            = uu____2422;
                                                          FStar_Tactics_Types.opts
                                                            =
                                                            (uu___112_2420.FStar_Tactics_Types.opts);
                                                          FStar_Tactics_Types.is_guard
                                                            = false
                                                        } in
                                                      [uu____2419] in
                                                    add_goals uu____2416))
                                        | t -> ret ()))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2481 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2481 with
           | (tm1,typ,guard) ->
               let uu____2493 =
                 let uu____2496 =
                   let uu____2499 = __apply uopt tm1 typ in
                   bind uu____2499
                     (fun uu____2503  ->
                        add_goal_from_guard goal.FStar_Tactics_Types.context
                          guard goal.FStar_Tactics_Types.opts) in
                 focus uu____2496 in
               let uu____2504 =
                 let uu____2507 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context tm1 in
                 let uu____2508 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context typ in
                 let uu____2509 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context
                     goal.FStar_Tactics_Types.goal_ty in
                 fail3
                   "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                   uu____2507 uu____2508 uu____2509 in
               try_unif uu____2493 uu____2504)
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2518 =
      let is_unit_t t =
        let uu____2525 =
          let uu____2526 = FStar_Syntax_Subst.compress t in
          uu____2526.FStar_Syntax_Syntax.n in
        match uu____2525 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
            true
        | uu____2530 -> false in
      bind cur_goal
        (fun goal  ->
           let uu____2540 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2540 with
           | (tm1,t,guard) ->
               let uu____2552 = FStar_Syntax_Util.arrow_formals_comp t in
               (match uu____2552 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2582 =
                         FStar_List.fold_left
                           (fun uu____2628  ->
                              fun uu____2629  ->
                                match (uu____2628, uu____2629) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2732 = is_unit_t b_t in
                                    if uu____2732
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____2770 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.FStar_Tactics_Types.context
                                           b_t in
                                       match uu____2770 with
                                       | (u,uu____2800,g_u) ->
                                           let uu____2814 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____2814,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2582 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____2884 =
                             let uu____2893 =
                               let uu____2902 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____2902.FStar_Syntax_Syntax.effect_args in
                             match uu____2893 with
                             | pre::post::uu____2913 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____2954 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____2884 with
                            | (pre,post) ->
                                let uu____2983 =
                                  let uu____2984 =
                                    let uu____2985 =
                                      FStar_Syntax_Util.mk_squash post in
                                    do_unify goal.FStar_Tactics_Types.context
                                      uu____2985
                                      goal.FStar_Tactics_Types.goal_ty in
                                  Prims.op_Negation uu____2984 in
                                if uu____2983
                                then
                                  let uu____2988 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context tm1 in
                                  let uu____2989 =
                                    let uu____2990 =
                                      FStar_Syntax_Util.mk_squash post in
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context
                                      uu____2990 in
                                  let uu____2991 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context
                                      goal.FStar_Tactics_Types.goal_ty in
                                  fail3
                                    "apply_lemma: Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                    uu____2988 uu____2989 uu____2991
                                else
                                  (let solution =
                                     let uu____2994 =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       goal.FStar_Tactics_Types.context
                                       uu____2994 in
                                   let implicits1 =
                                     FStar_All.pipe_right
                                       implicits.FStar_TypeChecker_Env.implicits
                                       (FStar_List.filter
                                          (fun uu____3062  ->
                                             match uu____3062 with
                                             | (uu____3075,uu____3076,uu____3077,tm2,uu____3079,uu____3080)
                                                 ->
                                                 let uu____3081 =
                                                   FStar_Syntax_Util.head_and_args
                                                     tm2 in
                                                 (match uu____3081 with
                                                  | (hd1,uu____3097) ->
                                                      let uu____3118 =
                                                        let uu____3119 =
                                                          FStar_Syntax_Subst.compress
                                                            hd1 in
                                                        uu____3119.FStar_Syntax_Syntax.n in
                                                      (match uu____3118 with
                                                       | FStar_Syntax_Syntax.Tm_uvar
                                                           uu____3122 -> true
                                                       | uu____3139 -> false)))) in
                                   let uu____3140 = solve goal solution in
                                   bind uu____3140
                                     (fun uu____3145  ->
                                        let uu____3146 =
                                          add_implicits implicits1 in
                                        bind uu____3146
                                          (fun uu____3157  ->
                                             let is_free_uvar uv t1 =
                                               let free_uvars =
                                                 let uu____3168 =
                                                   let uu____3175 =
                                                     FStar_Syntax_Free.uvars
                                                       t1 in
                                                   FStar_Util.set_elements
                                                     uu____3175 in
                                                 FStar_List.map
                                                   FStar_Pervasives_Native.fst
                                                   uu____3168 in
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
                                               let uu____3216 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t1 in
                                               match uu____3216 with
                                               | (hd1,uu____3232) ->
                                                   (match hd1.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_uvar
                                                        (uv,uu____3254) ->
                                                        appears uv goals
                                                    | uu____3279 -> false) in
                                             let sub_goals =
                                               FStar_All.pipe_right
                                                 implicits1
                                                 (FStar_List.map
                                                    (fun uu____3321  ->
                                                       match uu____3321 with
                                                       | (_msg,_env,_uvar,term,typ,uu____3339)
                                                           ->
                                                           let uu___115_3340
                                                             = goal in
                                                           let uu____3341 =
                                                             bnorm
                                                               goal.FStar_Tactics_Types.context
                                                               term in
                                                           let uu____3342 =
                                                             bnorm
                                                               goal.FStar_Tactics_Types.context
                                                               typ in
                                                           {
                                                             FStar_Tactics_Types.context
                                                               =
                                                               (uu___115_3340.FStar_Tactics_Types.context);
                                                             FStar_Tactics_Types.witness
                                                               = uu____3341;
                                                             FStar_Tactics_Types.goal_ty
                                                               = uu____3342;
                                                             FStar_Tactics_Types.opts
                                                               =
                                                               (uu___115_3340.FStar_Tactics_Types.opts);
                                                             FStar_Tactics_Types.is_guard
                                                               =
                                                               (uu___115_3340.FStar_Tactics_Types.is_guard)
                                                           })) in
                                             let rec filter' f xs =
                                               match xs with
                                               | [] -> []
                                               | x::xs1 ->
                                                   let uu____3380 = f x xs1 in
                                                   if uu____3380
                                                   then
                                                     let uu____3383 =
                                                       filter' f xs1 in
                                                     x :: uu____3383
                                                   else filter' f xs1 in
                                             let sub_goals1 =
                                               filter'
                                                 (fun g  ->
                                                    fun goals  ->
                                                      let uu____3397 =
                                                        checkone
                                                          g.FStar_Tactics_Types.witness
                                                          goals in
                                                      Prims.op_Negation
                                                        uu____3397) sub_goals in
                                             let uu____3398 =
                                               add_goal_from_guard
                                                 goal.FStar_Tactics_Types.context
                                                 guard
                                                 goal.FStar_Tactics_Types.opts in
                                             bind uu____3398
                                               (fun uu____3403  ->
                                                  let uu____3404 =
                                                    let uu____3407 =
                                                      let uu____3408 =
                                                        let uu____3409 =
                                                          FStar_Syntax_Util.mk_squash
                                                            pre in
                                                        istrivial
                                                          goal.FStar_Tactics_Types.context
                                                          uu____3409 in
                                                      Prims.op_Negation
                                                        uu____3408 in
                                                    if uu____3407
                                                    then
                                                      add_irrelevant_goal
                                                        goal.FStar_Tactics_Types.context
                                                        pre
                                                        goal.FStar_Tactics_Types.opts
                                                    else ret () in
                                                  bind uu____3404
                                                    (fun uu____3414  ->
                                                       add_goals sub_goals1))))))))) in
    focus uu____2518
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3431 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3431 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3441::(e1,uu____3443)::(e2,uu____3445)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3504 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3527 = destruct_eq' typ in
    match uu____3527 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3557 = FStar_Syntax_Util.un_squash typ in
        (match uu____3557 with
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
        let uu____3615 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3615 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3663 = aux e' in
               FStar_Util.map_opt uu____3663
                 (fun uu____3687  ->
                    match uu____3687 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3708 = aux e in
      FStar_Util.map_opt uu____3708
        (fun uu____3732  ->
           match uu____3732 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____3793 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____3793
            (fun uu____3817  ->
               match uu____3817 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___116_3834 = bv in
                     let uu____3835 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___116_3834.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___116_3834.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3835
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___117_3844 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___117_3844.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___117_3844.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3859 = h in
         match uu____3859 with
         | (bv,uu____3863) ->
             let uu____3864 =
               FStar_All.pipe_left mlog
                 (fun uu____3874  ->
                    let uu____3875 = FStar_Syntax_Print.bv_to_string bv in
                    let uu____3876 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3875
                      uu____3876) in
             bind uu____3864
               (fun uu____3879  ->
                  let uu____3880 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____3880 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____3909 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____3909 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____3924 =
                             let uu____3925 = FStar_Syntax_Subst.compress x in
                             uu____3925.FStar_Syntax_Syntax.n in
                           (match uu____3924 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___118_3938 = bv1 in
                                  let uu____3939 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___118_3938.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___118_3938.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____3939
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____3945 =
                                  let uu___119_3946 = goal in
                                  let uu____3947 = push_bvs e0 (bv :: bvs1) in
                                  let uu____3948 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____3949 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____3947;
                                    FStar_Tactics_Types.witness = uu____3948;
                                    FStar_Tactics_Types.goal_ty = uu____3949;
                                    FStar_Tactics_Types.opts =
                                      (uu___119_3946.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___119_3946.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____3945
                            | uu____3950 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____3951 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3978 = b in
           match uu____3978 with
           | (bv,uu____3982) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___120_3986 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___120_3986.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___120_3986.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3990 =
                   let uu____3991 =
                     let uu____3998 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3998) in
                   FStar_Syntax_Syntax.NT uu____3991 in
                 [uu____3990] in
               let uu____3999 = subst_goal bv bv' s1 goal in
               (match uu____3999 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4019 = b in
         match uu____4019 with
         | (bv,uu____4023) ->
             let uu____4024 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4024 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4053 = FStar_Syntax_Util.type_u () in
                  (match uu____4053 with
                   | (ty,u) ->
                       let uu____4062 = new_uvar e0 ty in
                       bind uu____4062
                         (fun t'  ->
                            let bv'' =
                              let uu___121_4072 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_4072.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_4072.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4076 =
                                let uu____4077 =
                                  let uu____4084 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4084) in
                                FStar_Syntax_Syntax.NT uu____4077 in
                              [uu____4076] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___122_4092 = b1 in
                                   let uu____4093 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___122_4092.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___122_4092.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4093
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4099  ->
                                 let uu____4100 =
                                   let uu____4103 =
                                     let uu____4106 =
                                       let uu___123_4107 = goal in
                                       let uu____4108 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4109 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4108;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4109;
                                         FStar_Tactics_Types.opts =
                                           (uu___123_4107.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___123_4107.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4106] in
                                   add_goals uu____4103 in
                                 bind uu____4100
                                   (fun uu____4112  ->
                                      let uu____4113 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal e0 uu____4113
                                        goal.FStar_Tactics_Types.opts))))))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4119 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4119 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4141 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4141 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___124_4175 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___124_4175.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___124_4175.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4187 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4187 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4208 = FStar_Syntax_Print.bv_to_string x in
               let uu____4209 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4208 uu____4209
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4216 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4216 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4238 = FStar_Util.set_mem x fns_ty in
           if uu____4238
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4242 = new_uvar env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4242
                (fun u  ->
                   let uu____4248 =
                     let uu____4249 = trysolve goal u in
                     Prims.op_Negation uu____4249 in
                   if uu____4248
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___125_4254 = goal in
                        let uu____4255 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4255;
                          FStar_Tactics_Types.goal_ty =
                            (uu___125_4254.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___125_4254.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___125_4254.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4257  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4269 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4269 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4293  ->
                    let uu____4294 = clear b in
                    bind uu____4294
                      (fun uu____4298  ->
                         bind intro (fun uu____4300  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___126_4317 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___126_4317.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___126_4317.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___126_4317.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___126_4317.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4319  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___127_4336 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___127_4336.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___127_4336.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___127_4336.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___127_4336.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4338  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4380 = f x in
          bind uu____4380
            (fun y  ->
               let uu____4388 = mapM f xs in
               bind uu____4388 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4434 = FStar_Syntax_Subst.compress t in
          uu____4434.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4469 = ff hd1 in
              bind uu____4469
                (fun hd2  ->
                   let fa uu____4489 =
                     match uu____4489 with
                     | (a,q) ->
                         let uu____4502 = ff a in
                         bind uu____4502 (fun a1  -> ret (a1, q)) in
                   let uu____4515 = mapM fa args in
                   bind uu____4515
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4575 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4575 with
               | (bs1,t') ->
                   let uu____4584 =
                     let uu____4587 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4587 t' in
                   bind uu____4584
                     (fun t''  ->
                        let uu____4591 =
                          let uu____4592 =
                            let uu____4609 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4610 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4609, uu____4610, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4592 in
                        ret uu____4591))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4631 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___128_4635 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___128_4635.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___128_4635.FStar_Syntax_Syntax.vars)
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
            let uu____4664 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4664 with
            | (t1,lcomp,g) ->
                let uu____4676 =
                  (let uu____4679 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____4679) ||
                    (let uu____4681 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4681) in
                if uu____4676
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4688 = new_uvar env typ in
                   bind uu____4688
                     (fun ut  ->
                        log ps
                          (fun uu____4699  ->
                             let uu____4700 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4701 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4700 uu____4701);
                        (let uu____4702 =
                           let uu____4705 =
                             let uu____4706 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4706 typ t1 ut in
                           add_irrelevant_goal env uu____4705 opts in
                         bind uu____4702
                           (fun uu____4709  ->
                              let uu____4710 =
                                bind tau
                                  (fun uu____4715  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4710))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4736 =
           match ps.FStar_Tactics_Types.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4736 with
         | (g,gs) ->
             let gt1 = g.FStar_Tactics_Types.goal_ty in
             (log ps
                (fun uu____4773  ->
                   let uu____4774 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4774);
              bind dismiss_all
                (fun uu____4777  ->
                   let uu____4778 =
                     tac_bottom_fold_env
                       (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                       g.FStar_Tactics_Types.context gt1 in
                   bind uu____4778
                     (fun gt'  ->
                        log ps
                          (fun uu____4788  ->
                             let uu____4789 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4789);
                        (let uu____4790 = push_goals gs in
                         bind uu____4790
                           (fun uu____4794  ->
                              add_goals
                                [(let uu___129_4796 = g in
                                  {
                                    FStar_Tactics_Types.context =
                                      (uu___129_4796.FStar_Tactics_Types.context);
                                    FStar_Tactics_Types.witness =
                                      (uu___129_4796.FStar_Tactics_Types.witness);
                                    FStar_Tactics_Types.goal_ty = gt';
                                    FStar_Tactics_Types.opts =
                                      (uu___129_4796.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___129_4796.FStar_Tactics_Types.is_guard)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4816 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____4816 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4828 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4828 with
            | (hd1,args) ->
                let uu____4861 =
                  let uu____4874 =
                    let uu____4875 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4875.FStar_Syntax_Syntax.n in
                  (uu____4874, args) in
                (match uu____4861 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4889::(l,uu____4891)::(r,uu____4893)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4940 =
                       let uu____4941 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____4941 in
                     if uu____4940
                     then
                       let uu____4944 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____4945 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4944 uu____4945
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____4948) ->
                     let uu____4965 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____4965))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4973 =
         new_uvar g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
       bind uu____4973
         (fun u  ->
            let g' =
              let uu___130_4980 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___130_4980.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___130_4980.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___130_4980.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___130_4980.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____4983  ->
                 let uu____4984 =
                   let uu____4987 =
                     let uu____4988 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4988
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal g.FStar_Tactics_Types.context
                     uu____4987 g.FStar_Tactics_Types.opts in
                 bind uu____4984
                   (fun uu____4991  ->
                      let uu____4992 = add_goals [g'] in
                      bind uu____4992 (fun uu____4996  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___131_5013 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___131_5013.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___131_5013.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___131_5013.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___131_5013.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___131_5013.FStar_Tactics_Types.depth)
              })
       | uu____5014 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___132_5029 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___132_5029.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___132_5029.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___132_5029.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___132_5029.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___132_5029.FStar_Tactics_Types.depth)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5036 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____5078 =
           (g.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
             g.FStar_Tactics_Types.context t in
         match uu____5078 with
         | (t1,typ,guard) ->
             let uu____5094 = FStar_Syntax_Util.head_and_args typ in
             (match uu____5094 with
              | (hd1,args) ->
                  let uu____5137 =
                    let uu____5150 =
                      let uu____5151 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____5151.FStar_Syntax_Syntax.n in
                    (uu____5150, args) in
                  (match uu____5137 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____5170)::(q,uu____5172)::[]) when
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
                         let uu___133_5210 = g in
                         let uu____5211 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_p in
                         {
                           FStar_Tactics_Types.context = uu____5211;
                           FStar_Tactics_Types.witness =
                             (uu___133_5210.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___133_5210.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___133_5210.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___133_5210.FStar_Tactics_Types.is_guard)
                         } in
                       let g2 =
                         let uu___134_5213 = g in
                         let uu____5214 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_q in
                         {
                           FStar_Tactics_Types.context = uu____5214;
                           FStar_Tactics_Types.witness =
                             (uu___134_5213.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___134_5213.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___134_5213.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___134_5213.FStar_Tactics_Types.is_guard)
                         } in
                       bind dismiss
                         (fun uu____5221  ->
                            let uu____5222 = add_goals [g1; g2] in
                            bind uu____5222
                              (fun uu____5231  ->
                                 let uu____5232 =
                                   let uu____5237 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____5238 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____5237, uu____5238) in
                                 ret uu____5232))
                   | uu____5243 ->
                       let uu____5256 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context typ in
                       fail1 "Not a disjunction: %s" uu____5256)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5279 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5279);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___135_5286 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___135_5286.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___135_5286.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___135_5286.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___135_5286.FStar_Tactics_Types.is_guard)
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
           let uu____5327 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               env tm in
           match uu____5327 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5356 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5362 =
              let uu____5363 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5363 in
            new_uvar env uu____5362 in
      bind uu____5356
        (fun typ  ->
           let uu____5375 = new_uvar env typ in
           bind uu____5375 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5395 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5395)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5415  ->
             let uu____5416 = FStar_Options.unsafe_tactic_exec () in
             if uu____5416
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5422  -> fun uu____5423  -> false) in
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
      let uu____5445 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5445 with
      | (u,uu____5463,g_u) ->
          let g =
            let uu____5478 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5478;
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
      let uu____5495 = goal_of_goal_ty env typ in
      match uu____5495 with
      | (g,g_u) ->
          let ps =
            {
              FStar_Tactics_Types.main_context = env;
              FStar_Tactics_Types.main_goal = g;
              FStar_Tactics_Types.all_implicits =
                (g_u.FStar_TypeChecker_Env.implicits);
              FStar_Tactics_Types.goals = [g];
              FStar_Tactics_Types.smt_goals = [];
              FStar_Tactics_Types.depth = (Prims.parse_int "0")
            } in
          (ps, (g.FStar_Tactics_Types.witness))