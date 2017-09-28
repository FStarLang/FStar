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
          ((let uu____580 =
              let uu____583 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____583 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____580);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail: 'Auu____623 . Prims.string -> 'Auu____623 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____634 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____634
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____642 . Prims.string -> Prims.string -> 'Auu____642 tac =
  fun msg  ->
    fun x  -> let uu____653 = FStar_Util.format1 msg x in fail uu____653
let fail2:
  'Auu____662 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____662 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____677 = FStar_Util.format2 msg x y in fail uu____677
let fail3:
  'Auu____688 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____688 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____707 = FStar_Util.format3 msg x y z in fail uu____707
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____735 = run t ps in
         match uu____735 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success
                ((FStar_Pervasives_Native.Some a), q))
         | FStar_Tactics_Result.Failed (uu____749,uu____750) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____765  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____783 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____797 =
         let uu___92_798 = p in
         let uu____799 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___92_798.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___92_798.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___92_798.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____799;
           FStar_Tactics_Types.smt_goals =
             (uu___92_798.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___92_798.FStar_Tactics_Types.depth)
         } in
       set uu____797)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____814 = trysolve goal solution in
      if uu____814
      then dismiss
      else
        (let uu____818 =
           let uu____819 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____820 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____821 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____819 uu____820
             uu____821 in
         fail uu____818)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___93_828 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___93_828.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___93_828.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___93_828.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___93_828.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___93_828.FStar_Tactics_Types.depth)
          }))
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___94_845 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___94_845.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___94_845.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___94_845.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___94_845.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___94_845.FStar_Tactics_Types.depth)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___95_862 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___95_862.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___95_862.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___95_862.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___95_862.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___95_862.FStar_Tactics_Types.depth)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___96_879 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___96_879.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___96_879.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___96_879.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___96_879.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___96_879.FStar_Tactics_Types.depth)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___97_896 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___97_896.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___97_896.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___97_896.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___97_896.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___97_896.FStar_Tactics_Types.depth)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____906  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___98_919 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___98_919.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___98_919.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___98_919.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___98_919.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___98_919.FStar_Tactics_Types.depth)
            }))
let new_uvar: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun typ  ->
      let uu____944 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____944 with
      | (u,uu____960,g_u) ->
          let uu____974 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____974 (fun uu____978  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____983 = FStar_Syntax_Util.un_squash t in
    match uu____983 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____993 =
          let uu____994 = FStar_Syntax_Subst.compress t' in
          uu____994.FStar_Syntax_Syntax.n in
        (match uu____993 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____998 -> false)
    | uu____999 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1008 = FStar_Syntax_Util.un_squash t in
    match uu____1008 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1018 =
          let uu____1019 = FStar_Syntax_Subst.compress t' in
          uu____1019.FStar_Syntax_Syntax.n in
        (match uu____1018 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1023 -> false)
    | uu____1024 -> false
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
        let uu____1058 = new_uvar env typ in
        bind uu____1058
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
        let uu____1081 = mk_irrelevant_goal env phi opts in
        bind uu____1081 (fun goal  -> add_goals [goal])
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
       let uu____1103 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1103
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1107 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1107))
let add_goal_from_guard:
  env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Options.optionstate -> Prims.unit tac
  =
  fun e  ->
    fun g  ->
      fun opts  ->
        let uu____1124 =
          let uu____1125 = FStar_TypeChecker_Rel.simplify_guard e g in
          uu____1125.FStar_TypeChecker_Env.guard_f in
        match uu____1124 with
        | FStar_TypeChecker_Common.Trivial  -> ret ()
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____1129 = istrivial e f in
            if uu____1129
            then ret ()
            else
              (let uu____1133 = mk_irrelevant_goal e f opts in
               bind uu____1133
                 (fun goal  ->
                    let goal1 =
                      let uu___99_1140 = goal in
                      {
                        FStar_Tactics_Types.context =
                          (uu___99_1140.FStar_Tactics_Types.context);
                        FStar_Tactics_Types.witness =
                          (uu___99_1140.FStar_Tactics_Types.witness);
                        FStar_Tactics_Types.goal_ty =
                          (uu___99_1140.FStar_Tactics_Types.goal_ty);
                        FStar_Tactics_Types.opts =
                          (uu___99_1140.FStar_Tactics_Types.opts);
                        FStar_Tactics_Types.is_guard = true
                      } in
                    push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1146 = is_irrelevant g in
       if uu____1146
       then bind dismiss (fun uu____1150  -> add_smt_goals [g])
       else
         (let uu____1152 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1152))
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
             let uu____1198 =
               try
                 let uu____1232 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1232
               with | uu____1262 -> fail "divide: not enough goals" in
             bind uu____1198
               (fun uu____1289  ->
                  match uu____1289 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___100_1315 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___100_1315.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___100_1315.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___100_1315.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___100_1315.FStar_Tactics_Types.depth)
                        } in
                      let rp =
                        let uu___101_1317 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___101_1317.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___101_1317.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___101_1317.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___101_1317.FStar_Tactics_Types.depth)
                        } in
                      let uu____1318 = set lp in
                      bind uu____1318
                        (fun uu____1326  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1340 = set rp in
                                     bind uu____1340
                                       (fun uu____1348  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___102_1364 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___102_1364.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___102_1364.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___102_1364.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___102_1364.FStar_Tactics_Types.depth)
                                                      } in
                                                    let uu____1365 = set p' in
                                                    bind uu____1365
                                                      (fun uu____1373  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1393 = divide (Prims.parse_int "1") f idtac in
    bind uu____1393
      (fun uu____1406  -> match uu____1406 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1441::uu____1442 ->
             let uu____1445 =
               let uu____1454 = map tau in
               divide (Prims.parse_int "1") tau uu____1454 in
             bind uu____1445
               (fun uu____1472  ->
                  match uu____1472 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1511 =
        bind t1
          (fun uu____1516  ->
             let uu____1517 = map t2 in
             bind uu____1517 (fun uu____1525  -> ret ())) in
      focus uu____1511
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1536 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1536 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1551 =
             let uu____1552 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1552 in
           if uu____1551
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1558 = new_uvar env' typ' in
              bind uu____1558
                (fun u  ->
                   let uu____1565 =
                     let uu____1566 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1566 in
                   if uu____1565
                   then
                     let uu____1569 =
                       let uu____1572 =
                         let uu___105_1573 = goal in
                         let uu____1574 = bnorm env' u in
                         let uu____1575 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1574;
                           FStar_Tactics_Types.goal_ty = uu____1575;
                           FStar_Tactics_Types.opts =
                             (uu___105_1573.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___105_1573.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1572 in
                     bind uu____1569 (fun uu____1577  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1583 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1583)
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
       (let uu____1604 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1604 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1623 =
              let uu____1624 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1624 in
            if uu____1623
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1640 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1640; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1642 =
                 let uu____1645 = comp_to_typ c in new_uvar env' uu____1645 in
               bind uu____1642
                 (fun u  ->
                    let lb =
                      let uu____1661 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____1661 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1665 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1665 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____1702 =
                            let uu____1705 =
                              let uu___106_1706 = goal in
                              let uu____1707 = bnorm env' u in
                              let uu____1708 =
                                let uu____1709 = comp_to_typ c in
                                bnorm env' uu____1709 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____1707;
                                FStar_Tactics_Types.goal_ty = uu____1708;
                                FStar_Tactics_Types.opts =
                                  (uu___106_1706.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___106_1706.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____1705 in
                          bind uu____1702
                            (fun uu____1716  ->
                               let uu____1717 =
                                 let uu____1722 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____1722, b) in
                               ret uu____1717)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____1736 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1736))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____1761 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1761 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___107_1768 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___107_1768.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___107_1768.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___107_1768.FStar_Tactics_Types.is_guard)
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
             let uu____1792 = FStar_TypeChecker_Normalize.tr_norm_steps s in
             FStar_List.append
               [FStar_TypeChecker_Normalize.Reify;
               FStar_TypeChecker_Normalize.UnfoldTac] uu____1792 in
           let t1 = normalize steps ps.FStar_Tactics_Types.main_context t in
           ret t1)
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1807 =
           try
             let uu____1835 =
               (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
                 goal.FStar_Tactics_Types.context t in
             ret uu____1835
           with
           | e ->
               let uu____1862 = FStar_Syntax_Print.term_to_string t in
               let uu____1863 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1862
                 uu____1863 in
         bind uu____1807
           (fun uu____1881  ->
              match uu____1881 with
              | (t1,typ,guard) ->
                  let uu____1893 =
                    let uu____1894 =
                      let uu____1895 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1895 in
                    Prims.op_Negation uu____1894 in
                  if uu____1893
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1899 =
                       do_unify goal.FStar_Tactics_Types.context typ
                         goal.FStar_Tactics_Types.goal_ty in
                     if uu____1899
                     then solve goal t1
                     else
                       (let uu____1903 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context t1 in
                        let uu____1904 =
                          let uu____1905 =
                            bnorm goal.FStar_Tactics_Types.context typ in
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context uu____1905 in
                        let uu____1906 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context
                            goal.FStar_Tactics_Types.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1903 uu____1904 uu____1906))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  -> let uu____1915 = __exact t in focus uu____1915
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1929 =
           try
             let uu____1957 =
               FStar_TypeChecker_TcTerm.tc_term
                 goal.FStar_Tactics_Types.context t in
             ret uu____1957
           with
           | e ->
               let uu____1984 = FStar_Syntax_Print.term_to_string t in
               let uu____1985 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1984
                 uu____1985 in
         bind uu____1929
           (fun uu____2003  ->
              match uu____2003 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2021 =
                       let uu____2022 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2022 in
                     if uu____2021
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2026 =
                          let uu____2035 =
                            let uu____2044 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2044.FStar_Syntax_Syntax.effect_args in
                          match uu____2035 with
                          | pre::post::uu____2055 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2096 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2026 with
                        | (pre,post) ->
                            let uu____2125 =
                              do_unify goal.FStar_Tactics_Types.context post
                                goal.FStar_Tactics_Types.goal_ty in
                            if uu____2125
                            then
                              let uu____2128 = solve goal t1 in
                              bind uu____2128
                                (fun uu____2132  ->
                                   add_irrelevant_goal
                                     goal.FStar_Tactics_Types.context pre
                                     goal.FStar_Tactics_Types.opts)
                            else
                              (let uu____2134 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context t1 in
                               let uu____2135 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context post in
                               let uu____2136 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2134 uu____2135 uu____2136)))))
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2149 =
             let uu____2156 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2156 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2149 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2183 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2203 =
               let uu____2208 = __exact tm in trytac uu____2208 in
             bind uu____2203
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2221 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2221 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           let uu____2251 =
                             let uu____2252 =
                               FStar_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu____2252 in
                           if uu____2251
                           then fail "apply: not total codomain"
                           else
                             (let uu____2256 =
                                new_uvar goal.FStar_Tactics_Types.context
                                  bv.FStar_Syntax_Syntax.sort in
                              bind uu____2256
                                (fun u  ->
                                   let tm' =
                                     FStar_Syntax_Syntax.mk_Tm_app tm
                                       [(u, aq)] FStar_Pervasives_Native.None
                                       (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                   let typ' =
                                     let uu____2276 = comp_to_typ c in
                                     FStar_All.pipe_left
                                       (FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.NT (bv, u)])
                                       uu____2276 in
                                   let uu____2277 = __apply uopt tm' typ' in
                                   bind uu____2277
                                     (fun uu____2285  ->
                                        let u1 =
                                          bnorm
                                            goal.FStar_Tactics_Types.context
                                            u in
                                        let uu____2287 =
                                          let uu____2288 =
                                            let uu____2291 =
                                              let uu____2292 =
                                                FStar_Syntax_Util.head_and_args
                                                  u1 in
                                              FStar_Pervasives_Native.fst
                                                uu____2292 in
                                            FStar_Syntax_Subst.compress
                                              uu____2291 in
                                          uu____2288.FStar_Syntax_Syntax.n in
                                        match uu____2287 with
                                        | FStar_Syntax_Syntax.Tm_uvar
                                            (uvar,uu____2320) ->
                                            bind get
                                              (fun ps  ->
                                                 let uu____2348 =
                                                   uopt &&
                                                     (uvar_free uvar ps) in
                                                 if uu____2348
                                                 then ret ()
                                                 else
                                                   (let uu____2352 =
                                                      let uu____2355 =
                                                        let uu___112_2356 =
                                                          goal in
                                                        let uu____2357 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            u1 in
                                                        let uu____2358 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          FStar_Tactics_Types.context
                                                            =
                                                            (uu___112_2356.FStar_Tactics_Types.context);
                                                          FStar_Tactics_Types.witness
                                                            = uu____2357;
                                                          FStar_Tactics_Types.goal_ty
                                                            = uu____2358;
                                                          FStar_Tactics_Types.opts
                                                            =
                                                            (uu___112_2356.FStar_Tactics_Types.opts);
                                                          FStar_Tactics_Types.is_guard
                                                            = false
                                                        } in
                                                      [uu____2355] in
                                                    add_goals uu____2352))
                                        | t -> ret ()))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2417 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2417 with
           | (tm1,typ,guard) ->
               let uu____2429 =
                 let uu____2432 =
                   let uu____2435 = __apply uopt tm1 typ in
                   bind uu____2435
                     (fun uu____2439  ->
                        add_goal_from_guard goal.FStar_Tactics_Types.context
                          guard goal.FStar_Tactics_Types.opts) in
                 focus uu____2432 in
               let uu____2440 =
                 let uu____2443 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context tm1 in
                 let uu____2444 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context typ in
                 let uu____2445 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context
                     goal.FStar_Tactics_Types.goal_ty in
                 fail3
                   "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                   uu____2443 uu____2444 uu____2445 in
               try_unif uu____2429 uu____2440)
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2454 =
      let is_unit_t t =
        let uu____2461 =
          let uu____2462 = FStar_Syntax_Subst.compress t in
          uu____2462.FStar_Syntax_Syntax.n in
        match uu____2461 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
            true
        | uu____2466 -> false in
      bind cur_goal
        (fun goal  ->
           let uu____2476 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2476 with
           | (tm1,t,guard) ->
               let uu____2488 = FStar_Syntax_Util.arrow_formals_comp t in
               (match uu____2488 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2518 =
                         FStar_List.fold_left
                           (fun uu____2564  ->
                              fun uu____2565  ->
                                match (uu____2564, uu____2565) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2668 = is_unit_t b_t in
                                    if uu____2668
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____2706 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.FStar_Tactics_Types.context
                                           b_t in
                                       match uu____2706 with
                                       | (u,uu____2736,g_u) ->
                                           let uu____2750 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____2750,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2518 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____2820 =
                             let uu____2829 =
                               let uu____2838 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____2838.FStar_Syntax_Syntax.effect_args in
                             match uu____2829 with
                             | pre::post::uu____2849 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____2890 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____2820 with
                            | (pre,post) ->
                                let uu____2919 =
                                  let uu____2920 =
                                    let uu____2921 =
                                      FStar_Syntax_Util.mk_squash post in
                                    do_unify goal.FStar_Tactics_Types.context
                                      uu____2921
                                      goal.FStar_Tactics_Types.goal_ty in
                                  Prims.op_Negation uu____2920 in
                                if uu____2919
                                then
                                  let uu____2924 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context tm1 in
                                  let uu____2925 =
                                    let uu____2926 =
                                      FStar_Syntax_Util.mk_squash post in
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context
                                      uu____2926 in
                                  let uu____2927 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context
                                      goal.FStar_Tactics_Types.goal_ty in
                                  fail3
                                    "apply_lemma: Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                    uu____2924 uu____2925 uu____2927
                                else
                                  (let solution =
                                     let uu____2930 =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       goal.FStar_Tactics_Types.context
                                       uu____2930 in
                                   let implicits1 =
                                     FStar_All.pipe_right
                                       implicits.FStar_TypeChecker_Env.implicits
                                       (FStar_List.filter
                                          (fun uu____2998  ->
                                             match uu____2998 with
                                             | (uu____3011,uu____3012,uu____3013,tm2,uu____3015,uu____3016)
                                                 ->
                                                 let uu____3017 =
                                                   FStar_Syntax_Util.head_and_args
                                                     tm2 in
                                                 (match uu____3017 with
                                                  | (hd1,uu____3033) ->
                                                      let uu____3054 =
                                                        let uu____3055 =
                                                          FStar_Syntax_Subst.compress
                                                            hd1 in
                                                        uu____3055.FStar_Syntax_Syntax.n in
                                                      (match uu____3054 with
                                                       | FStar_Syntax_Syntax.Tm_uvar
                                                           uu____3058 -> true
                                                       | uu____3075 -> false)))) in
                                   let uu____3076 = solve goal solution in
                                   bind uu____3076
                                     (fun uu____3081  ->
                                        let uu____3082 =
                                          add_implicits implicits1 in
                                        bind uu____3082
                                          (fun uu____3093  ->
                                             let is_free_uvar uv t1 =
                                               let free_uvars =
                                                 let uu____3104 =
                                                   let uu____3111 =
                                                     FStar_Syntax_Free.uvars
                                                       t1 in
                                                   FStar_Util.set_elements
                                                     uu____3111 in
                                                 FStar_List.map
                                                   FStar_Pervasives_Native.fst
                                                   uu____3104 in
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
                                               let uu____3152 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t1 in
                                               match uu____3152 with
                                               | (hd1,uu____3168) ->
                                                   (match hd1.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_uvar
                                                        (uv,uu____3190) ->
                                                        appears uv goals
                                                    | uu____3215 -> false) in
                                             let sub_goals =
                                               FStar_All.pipe_right
                                                 implicits1
                                                 (FStar_List.map
                                                    (fun uu____3257  ->
                                                       match uu____3257 with
                                                       | (_msg,_env,_uvar,term,typ,uu____3275)
                                                           ->
                                                           let uu___115_3276
                                                             = goal in
                                                           let uu____3277 =
                                                             bnorm
                                                               goal.FStar_Tactics_Types.context
                                                               term in
                                                           let uu____3278 =
                                                             bnorm
                                                               goal.FStar_Tactics_Types.context
                                                               typ in
                                                           {
                                                             FStar_Tactics_Types.context
                                                               =
                                                               (uu___115_3276.FStar_Tactics_Types.context);
                                                             FStar_Tactics_Types.witness
                                                               = uu____3277;
                                                             FStar_Tactics_Types.goal_ty
                                                               = uu____3278;
                                                             FStar_Tactics_Types.opts
                                                               =
                                                               (uu___115_3276.FStar_Tactics_Types.opts);
                                                             FStar_Tactics_Types.is_guard
                                                               =
                                                               (uu___115_3276.FStar_Tactics_Types.is_guard)
                                                           })) in
                                             let rec filter' f xs =
                                               match xs with
                                               | [] -> []
                                               | x::xs1 ->
                                                   let uu____3316 = f x xs1 in
                                                   if uu____3316
                                                   then
                                                     let uu____3319 =
                                                       filter' f xs1 in
                                                     x :: uu____3319
                                                   else filter' f xs1 in
                                             let sub_goals1 =
                                               filter'
                                                 (fun g  ->
                                                    fun goals  ->
                                                      let uu____3333 =
                                                        checkone
                                                          g.FStar_Tactics_Types.witness
                                                          goals in
                                                      Prims.op_Negation
                                                        uu____3333) sub_goals in
                                             let uu____3334 =
                                               add_goal_from_guard
                                                 goal.FStar_Tactics_Types.context
                                                 guard
                                                 goal.FStar_Tactics_Types.opts in
                                             bind uu____3334
                                               (fun uu____3339  ->
                                                  let uu____3340 =
                                                    let uu____3343 =
                                                      let uu____3344 =
                                                        let uu____3345 =
                                                          FStar_Syntax_Util.mk_squash
                                                            pre in
                                                        istrivial
                                                          goal.FStar_Tactics_Types.context
                                                          uu____3345 in
                                                      Prims.op_Negation
                                                        uu____3344 in
                                                    if uu____3343
                                                    then
                                                      add_irrelevant_goal
                                                        goal.FStar_Tactics_Types.context
                                                        pre
                                                        goal.FStar_Tactics_Types.opts
                                                    else ret () in
                                                  bind uu____3340
                                                    (fun uu____3350  ->
                                                       add_goals sub_goals1))))))))) in
    focus uu____2454
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3367 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3367 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3377::(e1,uu____3379)::(e2,uu____3381)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3440 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3463 = destruct_eq' typ in
    match uu____3463 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3493 = FStar_Syntax_Util.un_squash typ in
        (match uu____3493 with
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
        let uu____3551 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3551 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3599 = aux e' in
               FStar_Util.map_opt uu____3599
                 (fun uu____3623  ->
                    match uu____3623 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3644 = aux e in
      FStar_Util.map_opt uu____3644
        (fun uu____3668  ->
           match uu____3668 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____3729 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____3729
            (fun uu____3753  ->
               match uu____3753 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___116_3770 = bv in
                     let uu____3771 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___116_3770.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___116_3770.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3771
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___117_3780 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___117_3780.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___117_3780.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3795 = h in
         match uu____3795 with
         | (bv,uu____3799) ->
             let uu____3800 =
               FStar_All.pipe_left mlog
                 (fun uu____3810  ->
                    let uu____3811 = FStar_Syntax_Print.bv_to_string bv in
                    let uu____3812 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3811
                      uu____3812) in
             bind uu____3800
               (fun uu____3815  ->
                  let uu____3816 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____3816 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____3845 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____3845 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____3860 =
                             let uu____3861 = FStar_Syntax_Subst.compress x in
                             uu____3861.FStar_Syntax_Syntax.n in
                           (match uu____3860 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___118_3874 = bv1 in
                                  let uu____3875 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___118_3874.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___118_3874.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____3875
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____3881 =
                                  let uu___119_3882 = goal in
                                  let uu____3883 = push_bvs e0 (bv :: bvs1) in
                                  let uu____3884 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____3885 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____3883;
                                    FStar_Tactics_Types.witness = uu____3884;
                                    FStar_Tactics_Types.goal_ty = uu____3885;
                                    FStar_Tactics_Types.opts =
                                      (uu___119_3882.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___119_3882.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____3881
                            | uu____3886 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____3887 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3914 = b in
           match uu____3914 with
           | (bv,uu____3918) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___120_3922 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___120_3922.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___120_3922.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3926 =
                   let uu____3927 =
                     let uu____3934 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3934) in
                   FStar_Syntax_Syntax.NT uu____3927 in
                 [uu____3926] in
               let uu____3935 = subst_goal bv bv' s1 goal in
               (match uu____3935 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____3955 = b in
         match uu____3955 with
         | (bv,uu____3959) ->
             let uu____3960 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____3960 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____3989 = FStar_Syntax_Util.type_u () in
                  (match uu____3989 with
                   | (ty,u) ->
                       let uu____3998 = new_uvar e0 ty in
                       bind uu____3998
                         (fun t'  ->
                            let bv'' =
                              let uu___121_4008 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_4008.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_4008.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4012 =
                                let uu____4013 =
                                  let uu____4020 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4020) in
                                FStar_Syntax_Syntax.NT uu____4013 in
                              [uu____4012] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___122_4028 = b1 in
                                   let uu____4029 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___122_4028.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___122_4028.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4029
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4035  ->
                                 let uu____4036 =
                                   let uu____4039 =
                                     let uu____4042 =
                                       let uu___123_4043 = goal in
                                       let uu____4044 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4045 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4044;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4045;
                                         FStar_Tactics_Types.opts =
                                           (uu___123_4043.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___123_4043.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4042] in
                                   add_goals uu____4039 in
                                 bind uu____4036
                                   (fun uu____4048  ->
                                      let uu____4049 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal e0 uu____4049
                                        goal.FStar_Tactics_Types.opts))))))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4055 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4055 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4077 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4077 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___124_4111 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___124_4111.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___124_4111.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4123 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4123 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4144 = FStar_Syntax_Print.bv_to_string x in
               let uu____4145 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4144 uu____4145
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4152 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4152 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4174 = FStar_Util.set_mem x fns_ty in
           if uu____4174
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4178 = new_uvar env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4178
                (fun u  ->
                   let uu____4184 =
                     let uu____4185 = trysolve goal u in
                     Prims.op_Negation uu____4185 in
                   if uu____4184
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___125_4190 = goal in
                        let uu____4191 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4191;
                          FStar_Tactics_Types.goal_ty =
                            (uu___125_4190.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___125_4190.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___125_4190.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4193  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4205 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4205 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4229  ->
                    let uu____4230 = clear b in
                    bind uu____4230
                      (fun uu____4234  ->
                         bind intro (fun uu____4236  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___126_4253 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___126_4253.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___126_4253.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___126_4253.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___126_4253.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4255  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___127_4272 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___127_4272.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___127_4272.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___127_4272.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___127_4272.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4274  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4316 = f x in
          bind uu____4316
            (fun y  ->
               let uu____4324 = mapM f xs in
               bind uu____4324 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4370 = FStar_Syntax_Subst.compress t in
          uu____4370.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4405 = ff hd1 in
              bind uu____4405
                (fun hd2  ->
                   let fa uu____4425 =
                     match uu____4425 with
                     | (a,q) ->
                         let uu____4438 = ff a in
                         bind uu____4438 (fun a1  -> ret (a1, q)) in
                   let uu____4451 = mapM fa args in
                   bind uu____4451
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4511 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4511 with
               | (bs1,t') ->
                   let uu____4520 =
                     let uu____4523 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4523 t' in
                   bind uu____4520
                     (fun t''  ->
                        let uu____4527 =
                          let uu____4528 =
                            let uu____4545 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4546 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4545, uu____4546, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4528 in
                        ret uu____4527))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4567 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___128_4571 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___128_4571.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___128_4571.FStar_Syntax_Syntax.vars)
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
            let uu____4600 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4600 with
            | (t1,lcomp,g) ->
                let uu____4612 =
                  (let uu____4615 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____4615) ||
                    (let uu____4617 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4617) in
                if uu____4612
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4624 = new_uvar env typ in
                   bind uu____4624
                     (fun ut  ->
                        log ps
                          (fun uu____4635  ->
                             let uu____4636 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4637 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4636 uu____4637);
                        (let uu____4638 =
                           let uu____4641 =
                             let uu____4642 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4642 typ t1 ut in
                           add_irrelevant_goal env uu____4641 opts in
                         bind uu____4638
                           (fun uu____4645  ->
                              let uu____4646 =
                                bind tau
                                  (fun uu____4651  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4646))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4672 =
           match ps.FStar_Tactics_Types.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4672 with
         | (g,gs) ->
             let gt1 = g.FStar_Tactics_Types.goal_ty in
             (log ps
                (fun uu____4709  ->
                   let uu____4710 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4710);
              bind dismiss_all
                (fun uu____4713  ->
                   let uu____4714 =
                     tac_bottom_fold_env
                       (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                       g.FStar_Tactics_Types.context gt1 in
                   bind uu____4714
                     (fun gt'  ->
                        log ps
                          (fun uu____4724  ->
                             let uu____4725 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4725);
                        (let uu____4726 = push_goals gs in
                         bind uu____4726
                           (fun uu____4730  ->
                              add_goals
                                [(let uu___129_4732 = g in
                                  {
                                    FStar_Tactics_Types.context =
                                      (uu___129_4732.FStar_Tactics_Types.context);
                                    FStar_Tactics_Types.witness =
                                      (uu___129_4732.FStar_Tactics_Types.witness);
                                    FStar_Tactics_Types.goal_ty = gt';
                                    FStar_Tactics_Types.opts =
                                      (uu___129_4732.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___129_4732.FStar_Tactics_Types.is_guard)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4752 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____4752 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4764 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4764 with
            | (hd1,args) ->
                let uu____4797 =
                  let uu____4810 =
                    let uu____4811 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4811.FStar_Syntax_Syntax.n in
                  (uu____4810, args) in
                (match uu____4797 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4825::(l,uu____4827)::(r,uu____4829)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4876 =
                       let uu____4877 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____4877 in
                     if uu____4876
                     then
                       let uu____4880 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____4881 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4880 uu____4881
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____4884) ->
                     let uu____4901 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____4901))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4909 =
         new_uvar g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
       bind uu____4909
         (fun u  ->
            let g' =
              let uu___130_4916 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___130_4916.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___130_4916.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___130_4916.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___130_4916.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____4919  ->
                 let uu____4920 =
                   let uu____4923 =
                     let uu____4924 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4924
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal g.FStar_Tactics_Types.context
                     uu____4923 g.FStar_Tactics_Types.opts in
                 bind uu____4920
                   (fun uu____4927  ->
                      let uu____4928 = add_goals [g'] in
                      bind uu____4928 (fun uu____4932  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___131_4949 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___131_4949.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___131_4949.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___131_4949.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___131_4949.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___131_4949.FStar_Tactics_Types.depth)
              })
       | uu____4950 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___132_4965 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___132_4965.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___132_4965.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___132_4965.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___132_4965.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___132_4965.FStar_Tactics_Types.depth)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____4972 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____5014 =
           (g.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
             g.FStar_Tactics_Types.context t in
         match uu____5014 with
         | (t1,typ,guard) ->
             let uu____5030 = FStar_Syntax_Util.head_and_args typ in
             (match uu____5030 with
              | (hd1,args) ->
                  let uu____5073 =
                    let uu____5086 =
                      let uu____5087 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____5087.FStar_Syntax_Syntax.n in
                    (uu____5086, args) in
                  (match uu____5073 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____5106)::(q,uu____5108)::[]) when
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
                         let uu___133_5146 = g in
                         let uu____5147 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_p in
                         {
                           FStar_Tactics_Types.context = uu____5147;
                           FStar_Tactics_Types.witness =
                             (uu___133_5146.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___133_5146.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___133_5146.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___133_5146.FStar_Tactics_Types.is_guard)
                         } in
                       let g2 =
                         let uu___134_5149 = g in
                         let uu____5150 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_q in
                         {
                           FStar_Tactics_Types.context = uu____5150;
                           FStar_Tactics_Types.witness =
                             (uu___134_5149.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___134_5149.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___134_5149.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___134_5149.FStar_Tactics_Types.is_guard)
                         } in
                       bind dismiss
                         (fun uu____5157  ->
                            let uu____5158 = add_goals [g1; g2] in
                            bind uu____5158
                              (fun uu____5167  ->
                                 let uu____5168 =
                                   let uu____5173 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____5174 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____5173, uu____5174) in
                                 ret uu____5168))
                   | uu____5179 ->
                       let uu____5192 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context typ in
                       fail1 "Not a disjunction: %s" uu____5192)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5215 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5215);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___135_5222 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___135_5222.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___135_5222.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___135_5222.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___135_5222.FStar_Tactics_Types.is_guard)
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
           let uu____5263 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               env tm in
           match uu____5263 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5292 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5298 =
              let uu____5299 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5299 in
            new_uvar env uu____5298 in
      bind uu____5292
        (fun typ  ->
           let uu____5311 = new_uvar env typ in
           bind uu____5311 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5331 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5331)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5351  ->
             let uu____5352 = FStar_Options.unsafe_tactic_exec () in
             if uu____5352
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5358  -> fun uu____5359  -> false) in
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
      let uu____5381 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5381 with
      | (u,uu____5399,g_u) ->
          let g =
            let uu____5414 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5414;
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
      let uu____5431 = goal_of_goal_ty env typ in
      match uu____5431 with
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