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
          let uu____315 =
            let uu____316 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____316 msg in
          let uu____317 =
            let uu____320 =
              let uu____321 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range in
              FStar_Util.format1 "Position: %s\n" uu____321 in
            let uu____322 =
              let uu____325 =
                let uu____326 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals) in
                let uu____327 =
                  let uu____328 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals in
                  FStar_String.concat "\n" uu____328 in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____326
                  uu____327 in
              let uu____331 =
                let uu____334 =
                  let uu____335 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals) in
                  let uu____336 =
                    let uu____337 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals in
                    FStar_String.concat "\n" uu____337 in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____335
                    uu____336 in
                [uu____334] in
              uu____325 :: uu____331 in
            uu____320 :: uu____322 in
          uu____315 :: uu____317 in
        FStar_String.concat "" uu____312
let goal_to_json: FStar_Tactics_Types.goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____345 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____345 FStar_Syntax_Print.binders_to_json in
    let uu____346 =
      let uu____353 =
        let uu____360 =
          let uu____365 =
            let uu____366 =
              let uu____373 =
                let uu____378 =
                  let uu____379 =
                    FStar_TypeChecker_Normalize.term_to_string
                      g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness in
                  FStar_Util.JsonStr uu____379 in
                ("witness", uu____378) in
              let uu____380 =
                let uu____387 =
                  let uu____392 =
                    let uu____393 =
                      FStar_TypeChecker_Normalize.term_to_string
                        g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty in
                    FStar_Util.JsonStr uu____393 in
                  ("type", uu____392) in
                [uu____387] in
              uu____373 :: uu____380 in
            FStar_Util.JsonAssoc uu____366 in
          ("goal", uu____365) in
        [uu____360] in
      ("hyps", g_binders) :: uu____353 in
    FStar_Util.JsonAssoc uu____346
let ps_to_json:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____425  ->
    match uu____425 with
    | (msg,ps) ->
        let uu____432 =
          let uu____439 =
            let uu____446 =
              let uu____451 =
                let uu____452 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals in
                FStar_Util.JsonList uu____452 in
              ("goals", uu____451) in
            let uu____455 =
              let uu____462 =
                let uu____467 =
                  let uu____468 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals in
                  FStar_Util.JsonList uu____468 in
                ("smt-goals", uu____467) in
              [uu____462] in
            uu____446 :: uu____455 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____439 in
        FStar_Util.JsonAssoc uu____432
let dump_proofstate:
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____497  ->
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
         (let uu____519 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_cur uu____519 msg);
         FStar_Tactics_Result.Success ((), ps))
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc in
         (let uu____536 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_proofstate uu____536 msg);
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
      let uu____567 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____567 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____621 =
              let uu____624 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____624 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____621);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'Auu____714 . Prims.string -> 'Auu____714 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____725 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____725
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____733 . Prims.string -> Prims.string -> 'Auu____733 tac =
  fun msg  ->
    fun x  -> let uu____744 = FStar_Util.format1 msg x in fail uu____744
let fail2:
  'Auu____753 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____753 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____768 = FStar_Util.format2 msg x y in fail uu____768
let fail3:
  'Auu____779 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____779 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____798 = FStar_Util.format3 msg x y z in fail uu____798
let trytac': 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____830 = run t ps in
         match uu____830 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____851) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____878 = trytac' t in
    bind uu____878
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____905 -> ret FStar_Pervasives_Native.None)
let wrap_err: 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____934 = run t ps in
           match uu____934 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____952  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____970 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____984 =
         let uu___136_985 = p in
         let uu____986 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___136_985.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___136_985.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___136_985.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____986;
           FStar_Tactics_Types.smt_goals =
             (uu___136_985.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___136_985.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___136_985.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___136_985.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___136_985.FStar_Tactics_Types.entry_range)
         } in
       set uu____984)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____1001 = trysolve goal solution in
      if uu____1001
      then dismiss
      else
        (let uu____1005 =
           let uu____1006 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____1007 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____1008 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____1006
             uu____1007 uu____1008 in
         fail uu____1005)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___137_1015 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___137_1015.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___137_1015.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___137_1015.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___137_1015.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___137_1015.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___137_1015.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___137_1015.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___137_1015.FStar_Tactics_Types.entry_range)
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
      let uu____1031 = FStar_TypeChecker_Env.pop_bv e in
      match uu____1031 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____1049 =
      let uu____1050 = aux b2 env in Prims.op_Negation uu____1050 in
    if uu____1049
    then
      let uu____1051 =
        let uu____1052 = goal_to_string g in
        FStar_Util.format1
          "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
          uu____1052 in
      FStar_Errors.warn
        (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____1051
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___138_1072 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___138_1072.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___138_1072.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___138_1072.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___138_1072.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___138_1072.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___138_1072.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___138_1072.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___138_1072.FStar_Tactics_Types.entry_range)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___139_1091 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___139_1091.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___139_1091.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___139_1091.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___139_1091.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___139_1091.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___139_1091.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___139_1091.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___139_1091.FStar_Tactics_Types.entry_range)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___140_1110 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___140_1110.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___140_1110.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___140_1110.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___140_1110.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___140_1110.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___140_1110.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___140_1110.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___140_1110.FStar_Tactics_Types.entry_range)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___141_1129 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___141_1129.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___141_1129.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___141_1129.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___141_1129.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___141_1129.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___141_1129.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___141_1129.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___141_1129.FStar_Tactics_Types.entry_range)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1139  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___142_1152 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___142_1152.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___142_1152.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___142_1152.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___142_1152.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___142_1152.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___142_1152.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___142_1152.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___142_1152.FStar_Tactics_Types.entry_range)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1181 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1181 with
        | (u,uu____1197,g_u) ->
            let uu____1211 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1211 (fun uu____1215  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1220 = FStar_Syntax_Util.un_squash t in
    match uu____1220 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1230 =
          let uu____1231 = FStar_Syntax_Subst.compress t' in
          uu____1231.FStar_Syntax_Syntax.n in
        (match uu____1230 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1235 -> false)
    | uu____1236 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1245 = FStar_Syntax_Util.un_squash t in
    match uu____1245 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1255 =
          let uu____1256 = FStar_Syntax_Subst.compress t' in
          uu____1256.FStar_Syntax_Syntax.n in
        (match uu____1255 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1260 -> false)
    | uu____1261 -> false
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
          let uu____1299 = new_uvar reason env typ in
          bind uu____1299
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
             let uu____1357 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1357
           with | e1 -> fail "not typeable")
let must_trivial: env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1407 =
          let uu____1408 =
            let uu____1409 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1409 in
          Prims.op_Negation uu____1408 in
        if uu____1407 then fail "got non-trivial guard" else ret ()
      with | uu____1418 -> fail "got non-trivial guard"
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1427 =
      bind cur_goal
        (fun goal  ->
           let uu____1433 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1433
             (fun uu____1453  ->
                match uu____1453 with
                | (t1,typ,guard) ->
                    let uu____1465 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____1465 (fun uu____1469  -> ret typ))) in
    FStar_All.pipe_left (wrap_err "tc") uu____1427
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1494 = mk_irrelevant_goal reason env phi opts in
          bind uu____1494 (fun goal  -> add_goals [goal])
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
       let uu____1516 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1516
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1520 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1520))
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
          let uu____1541 =
            let uu____1542 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1542.FStar_TypeChecker_Env.guard_f in
          match uu____1541 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1546 = istrivial e f in
              if uu____1546
              then ret ()
              else
                (let uu____1550 = mk_irrelevant_goal reason e f opts in
                 bind uu____1550
                   (fun goal  ->
                      let goal1 =
                        let uu___147_1557 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___147_1557.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___147_1557.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___147_1557.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___147_1557.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard = true
                        } in
                      push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1563 = is_irrelevant g in
       if uu____1563
       then bind dismiss (fun uu____1567  -> add_smt_goals [g])
       else
         (let uu____1569 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1569))
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
             let uu____1615 =
               try
                 let uu____1649 =
                   let uu____1658 = FStar_BigInt.to_int_fs n1 in
                   FStar_List.splitAt uu____1658 p.FStar_Tactics_Types.goals in
                 ret uu____1649
               with | uu____1680 -> fail "divide: not enough goals" in
             bind uu____1615
               (fun uu____1707  ->
                  match uu____1707 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___148_1733 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___148_1733.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___148_1733.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___148_1733.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___148_1733.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___148_1733.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___148_1733.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___148_1733.FStar_Tactics_Types.entry_range)
                        } in
                      let rp =
                        let uu___149_1735 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___149_1735.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___149_1735.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___149_1735.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___149_1735.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___149_1735.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___149_1735.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___149_1735.FStar_Tactics_Types.entry_range)
                        } in
                      let uu____1736 = set lp in
                      bind uu____1736
                        (fun uu____1744  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1758 = set rp in
                                     bind uu____1758
                                       (fun uu____1766  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___150_1782 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___150_1782.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___150_1782.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___150_1782.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___150_1782.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___150_1782.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___150_1782.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___150_1782.FStar_Tactics_Types.entry_range)
                                                      } in
                                                    let uu____1783 = set p' in
                                                    bind uu____1783
                                                      (fun uu____1791  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1811 = divide FStar_BigInt.one f idtac in
    bind uu____1811
      (fun uu____1824  -> match uu____1824 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1859::uu____1860 ->
             let uu____1863 =
               let uu____1872 = map tau in
               divide FStar_BigInt.one tau uu____1872 in
             bind uu____1863
               (fun uu____1890  ->
                  match uu____1890 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1929 =
        bind t1
          (fun uu____1934  ->
             let uu____1935 = map t2 in
             bind uu____1935 (fun uu____1943  -> ret ())) in
      focus uu____1929
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1954 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1954 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1969 =
             let uu____1970 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1970 in
           if uu____1969
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1976 = new_uvar "intro" env' typ' in
              bind uu____1976
                (fun u  ->
                   let uu____1983 =
                     let uu____1984 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1984 in
                   if uu____1983
                   then
                     let uu____1987 =
                       let uu____1990 =
                         let uu___153_1991 = goal in
                         let uu____1992 = bnorm env' u in
                         let uu____1993 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1992;
                           FStar_Tactics_Types.goal_ty = uu____1993;
                           FStar_Tactics_Types.opts =
                             (uu___153_1991.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___153_1991.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1990 in
                     bind uu____1987 (fun uu____1995  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2001 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____2001)
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
       (let uu____2022 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____2022 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2041 =
              let uu____2042 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____2042 in
            if uu____2041
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____2058 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____2058; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____2060 =
                 let uu____2063 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____2063 in
               bind uu____2060
                 (fun u  ->
                    let lb =
                      let uu____2079 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2079 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2083 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2083 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2120 =
                            let uu____2123 =
                              let uu___154_2124 = goal in
                              let uu____2125 = bnorm env' u in
                              let uu____2126 =
                                let uu____2127 = comp_to_typ c in
                                bnorm env' uu____2127 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2125;
                                FStar_Tactics_Types.goal_ty = uu____2126;
                                FStar_Tactics_Types.opts =
                                  (uu___154_2124.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___154_2124.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2123 in
                          bind uu____2120
                            (fun uu____2134  ->
                               let uu____2135 =
                                 let uu____2140 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2140, b) in
                               ret uu____2135)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2154 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2154))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2179 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2179 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___155_2186 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___155_2186.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___155_2186.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___155_2186.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2207 =
          bind get
            (fun ps  ->
               let uu____2213 = __tc e t in
               bind uu____2213
                 (fun uu____2235  ->
                    match uu____2235 with
                    | (t1,uu____2245,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2251 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2251 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2207
let __exact: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun force_guard  ->
    fun t  ->
      bind cur_goal
        (fun goal  ->
           let uu____2274 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____2274
             (fun uu____2294  ->
                match uu____2294 with
                | (t1,typ,guard) ->
                    let uu____2306 =
                      if force_guard
                      then
                        must_trivial goal.FStar_Tactics_Types.context guard
                      else
                        add_goal_from_guard "__exact typing"
                          goal.FStar_Tactics_Types.context guard
                          goal.FStar_Tactics_Types.opts in
                    bind uu____2306
                      (fun uu____2314  ->
                         let uu____2315 =
                           do_unify goal.FStar_Tactics_Types.context typ
                             goal.FStar_Tactics_Types.goal_ty in
                         if uu____2315
                         then solve goal t1
                         else
                           (let uu____2319 =
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context t1 in
                            let uu____2320 =
                              let uu____2321 =
                                bnorm goal.FStar_Tactics_Types.context typ in
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context uu____2321 in
                            let uu____2322 =
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context
                                goal.FStar_Tactics_Types.goal_ty in
                            fail3
                              "%s : %s does not exactly solve the goal %s"
                              uu____2319 uu____2320 uu____2322))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2331 =
      mlog
        (fun uu____2336  ->
           let uu____2337 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact: tm = %s\n" uu____2337)
        (fun uu____2340  ->
           let uu____2341 = __exact true tm in focus uu____2341) in
    FStar_All.pipe_left (wrap_err "exact") uu____2331
let exact_guard: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2356 =
      mlog
        (fun uu____2361  ->
           let uu____2362 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact_guard: tm = %s\n" uu____2362)
        (fun uu____2365  ->
           let uu____2366 = __exact false tm in focus uu____2366) in
    FStar_All.pipe_left (wrap_err "exact_guard") uu____2356
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2385 =
             let uu____2392 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2392 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2385 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2419 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2439 =
               let uu____2444 = __exact true tm in trytac uu____2444 in
             bind uu____2439
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2457 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2457 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2489  ->
                                let uu____2490 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2490)
                             (fun uu____2493  ->
                                let uu____2494 =
                                  let uu____2495 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2495 in
                                if uu____2494
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2499 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2499
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2519 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2519 in
                                        let uu____2520 =
                                          __apply uopt tm' typ' in
                                        bind uu____2520
                                          (fun uu____2528  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2530 =
                                               let uu____2531 =
                                                 let uu____2534 =
                                                   let uu____2535 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2535 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2534 in
                                               uu____2531.FStar_Syntax_Syntax.n in
                                             match uu____2530 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2563) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2591 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2591
                                                      then ret ()
                                                      else
                                                        (let uu____2595 =
                                                           let uu____2598 =
                                                             let uu___156_2599
                                                               = goal in
                                                             let uu____2600 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2601 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___156_2599.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2600;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2601;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___156_2599.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2598] in
                                                         add_goals uu____2595))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2652 =
        mlog
          (fun uu____2657  ->
             let uu____2658 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2658)
          (fun uu____2660  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2664 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2664
                    (fun uu____2685  ->
                       match uu____2685 with
                       | (tm1,typ,guard) ->
                           let uu____2697 =
                             let uu____2700 =
                               let uu____2703 = __apply uopt tm1 typ in
                               bind uu____2703
                                 (fun uu____2707  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2700 in
                           let uu____2708 =
                             let uu____2711 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context tm1 in
                             let uu____2712 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context typ in
                             let uu____2713 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2711 uu____2712 uu____2713 in
                           try_unif uu____2697 uu____2708))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2652
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2726 =
      let uu____2729 =
        mlog
          (fun uu____2734  ->
             let uu____2735 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2735)
          (fun uu____2738  ->
             let is_unit_t t =
               let uu____2743 =
                 let uu____2744 = FStar_Syntax_Subst.compress t in
                 uu____2744.FStar_Syntax_Syntax.n in
               match uu____2743 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____2748 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____2752 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2752
                    (fun uu____2774  ->
                       match uu____2774 with
                       | (tm1,t,guard) ->
                           let uu____2786 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____2786 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____2816 =
                                     FStar_List.fold_left
                                       (fun uu____2862  ->
                                          fun uu____2863  ->
                                            match (uu____2862, uu____2863)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____2966 =
                                                  is_unit_t b_t in
                                                if uu____2966
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3004 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____3004 with
                                                   | (u,uu____3034,g_u) ->
                                                       let uu____3048 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____3048,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____2816 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3118 =
                                         let uu____3127 =
                                           let uu____3136 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3136.FStar_Syntax_Syntax.effect_args in
                                         match uu____3127 with
                                         | pre::post::uu____3147 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3188 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3118 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3220 =
                                                let uu____3229 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3229] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3220 in
                                            let uu____3230 =
                                              let uu____3231 =
                                                let uu____3232 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3232
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3231 in
                                            if uu____3230
                                            then
                                              let uu____3235 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3236 =
                                                let uu____3237 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3237 in
                                              let uu____3238 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3235 uu____3236
                                                uu____3238
                                            else
                                              (let solution =
                                                 let uu____3241 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3241 in
                                               let uu____3242 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3242
                                                 (fun uu____3248  ->
                                                    let implicits1 =
                                                      FStar_All.pipe_right
                                                        implicits.FStar_TypeChecker_Env.implicits
                                                        (FStar_List.filter
                                                           (fun uu____3316 
                                                              ->
                                                              match uu____3316
                                                              with
                                                              | (uu____3329,uu____3330,uu____3331,tm2,uu____3333,uu____3334)
                                                                  ->
                                                                  let uu____3335
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    tm2 in
                                                                  (match uu____3335
                                                                   with
                                                                   | 
                                                                   (hd1,uu____3351)
                                                                    ->
                                                                    let uu____3372
                                                                    =
                                                                    let uu____3373
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3373.FStar_Syntax_Syntax.n in
                                                                    (match uu____3372
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3376
                                                                    -> true
                                                                    | 
                                                                    uu____3393
                                                                    -> false)))) in
                                                    let uu____3394 =
                                                      solve goal solution in
                                                    bind uu____3394
                                                      (fun uu____3405  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3416 =
                                                               let uu____3423
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3423 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3416 in
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
                                                           let uu____3464 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3464
                                                           with
                                                           | (hd1,uu____3480)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3502)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3527
                                                                    -> false) in
                                                         let sub_goals =
                                                           FStar_All.pipe_right
                                                             implicits1
                                                             (FStar_List.map
                                                                (fun
                                                                   uu____3569
                                                                    ->
                                                                   match uu____3569
                                                                   with
                                                                   | 
                                                                   (_msg,_env,_uvar,term,typ,uu____3587)
                                                                    ->
                                                                    let uu___159_3588
                                                                    = goal in
                                                                    let uu____3589
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3590
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___159_3588.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3589;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3590;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___159_3588.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___159_3588.FStar_Tactics_Types.is_guard)
                                                                    })) in
                                                         let rec filter' f xs
                                                           =
                                                           match xs with
                                                           | [] -> []
                                                           | x::xs1 ->
                                                               let uu____3628
                                                                 = f x xs1 in
                                                               if uu____3628
                                                               then
                                                                 let uu____3631
                                                                   =
                                                                   filter' f
                                                                    xs1 in
                                                                 x ::
                                                                   uu____3631
                                                               else
                                                                 filter' f
                                                                   xs1 in
                                                         let sub_goals1 =
                                                           filter'
                                                             (fun g  ->
                                                                fun goals  ->
                                                                  let uu____3645
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                  Prims.op_Negation
                                                                    uu____3645)
                                                             sub_goals in
                                                         let uu____3646 =
                                                           add_goal_from_guard
                                                             "apply_lemma guard"
                                                             goal.FStar_Tactics_Types.context
                                                             guard
                                                             goal.FStar_Tactics_Types.opts in
                                                         bind uu____3646
                                                           (fun uu____3651 
                                                              ->
                                                              let uu____3652
                                                                =
                                                                let uu____3655
                                                                  =
                                                                  let uu____3656
                                                                    =
                                                                    let uu____3657
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____3657 in
                                                                  Prims.op_Negation
                                                                    uu____3656 in
                                                                if uu____3655
                                                                then
                                                                  add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                else ret () in
                                                              bind uu____3652
                                                                (fun
                                                                   uu____3662
                                                                    ->
                                                                   add_goals
                                                                    sub_goals1))))))))))) in
      focus uu____2729 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2726
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3683 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3683 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3693::(e1,uu____3695)::(e2,uu____3697)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3756 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3779 = destruct_eq' typ in
    match uu____3779 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3809 = FStar_Syntax_Util.un_squash typ in
        (match uu____3809 with
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
        let uu____3867 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3867 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3915 = aux e' in
               FStar_Util.map_opt uu____3915
                 (fun uu____3939  ->
                    match uu____3939 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3960 = aux e in
      FStar_Util.map_opt uu____3960
        (fun uu____3984  ->
           match uu____3984 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____4045 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____4045
            (fun uu____4069  ->
               match uu____4069 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___160_4086 = bv in
                     let uu____4087 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___160_4086.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___160_4086.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4087
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___161_4096 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___161_4096.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___161_4096.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4110 = h in
         match uu____4110 with
         | (bv,uu____4114) ->
             mlog
               (fun uu____4118  ->
                  let uu____4119 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4120 =
                    FStar_Syntax_Print.term_to_string
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4119
                    uu____4120)
               (fun uu____4123  ->
                  let uu____4124 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4124 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4153 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4153 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4168 =
                             let uu____4169 = FStar_Syntax_Subst.compress x in
                             uu____4169.FStar_Syntax_Syntax.n in
                           (match uu____4168 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___162_4182 = bv1 in
                                  let uu____4183 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___162_4182.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___162_4182.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4183
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4189 =
                                  let uu___163_4190 = goal in
                                  let uu____4191 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4192 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4193 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4191;
                                    FStar_Tactics_Types.witness = uu____4192;
                                    FStar_Tactics_Types.goal_ty = uu____4193;
                                    FStar_Tactics_Types.opts =
                                      (uu___163_4190.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___163_4190.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4189
                            | uu____4194 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4195 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4222 = b in
           match uu____4222 with
           | (bv,uu____4226) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___164_4230 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___164_4230.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___164_4230.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4234 =
                   let uu____4235 =
                     let uu____4242 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4242) in
                   FStar_Syntax_Syntax.NT uu____4235 in
                 [uu____4234] in
               let uu____4243 = subst_goal bv bv' s1 goal in
               (match uu____4243 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4263 = b in
         match uu____4263 with
         | (bv,uu____4267) ->
             let uu____4268 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4268 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4297 = FStar_Syntax_Util.type_u () in
                  (match uu____4297 with
                   | (ty,u) ->
                       let uu____4306 = new_uvar "binder_retype" e0 ty in
                       bind uu____4306
                         (fun t'  ->
                            let bv'' =
                              let uu___165_4316 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___165_4316.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___165_4316.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4320 =
                                let uu____4321 =
                                  let uu____4328 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4328) in
                                FStar_Syntax_Syntax.NT uu____4321 in
                              [uu____4320] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___166_4336 = b1 in
                                   let uu____4337 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___166_4336.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___166_4336.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4337
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4343  ->
                                 let uu____4344 =
                                   let uu____4347 =
                                     let uu____4350 =
                                       let uu___167_4351 = goal in
                                       let uu____4352 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4353 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4352;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4353;
                                         FStar_Tactics_Types.opts =
                                           (uu___167_4351.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___167_4351.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4350] in
                                   add_goals uu____4347 in
                                 bind uu____4344
                                   (fun uu____4356  ->
                                      let uu____4357 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4357
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4380 = b in
           match uu____4380 with
           | (bv,uu____4384) ->
               let uu____4385 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4385 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4417 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4417 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___168_4422 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___168_4422.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___168_4422.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___169_4426 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___169_4426.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___169_4426.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___169_4426.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___169_4426.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4432 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4432 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4454 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4454 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___170_4488 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___170_4488.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___170_4488.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4500 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4500 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4521 = FStar_Syntax_Print.bv_to_string x in
               let uu____4522 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4521 uu____4522
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4529 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4529 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4551 = FStar_Util.set_mem x fns_ty in
           if uu____4551
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4555 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4555
                (fun u  ->
                   let uu____4561 =
                     let uu____4562 = trysolve goal u in
                     Prims.op_Negation uu____4562 in
                   if uu____4561
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___171_4567 = goal in
                        let uu____4568 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4568;
                          FStar_Tactics_Types.goal_ty =
                            (uu___171_4567.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___171_4567.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___171_4567.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4570  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4582 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4582 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4606  ->
                    let uu____4607 = clear b in
                    bind uu____4607
                      (fun uu____4611  ->
                         bind intro (fun uu____4613  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___172_4630 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___172_4630.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___172_4630.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___172_4630.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___172_4630.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4632  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___173_4649 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___173_4649.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___173_4649.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___173_4649.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___173_4649.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4651  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4693 = f x in
          bind uu____4693
            (fun y  ->
               let uu____4701 = mapM f xs in
               bind uu____4701 (fun ys  -> ret (y :: ys)))
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
            let uu____4751 = FStar_Syntax_Subst.compress t in
            uu____4751.FStar_Syntax_Syntax.n in
          let uu____4754 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___175_4760 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___175_4760.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___175_4760.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____4754
            (fun t1  ->
               let tn1 =
                 let uu____4768 =
                   let uu____4769 = FStar_Syntax_Subst.compress t1 in
                   uu____4769.FStar_Syntax_Syntax.n in
                 match uu____4768 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____4801 = ff hd1 in
                     bind uu____4801
                       (fun hd2  ->
                          let fa uu____4821 =
                            match uu____4821 with
                            | (a,q) ->
                                let uu____4834 = ff a in
                                bind uu____4834 (fun a1  -> ret (a1, q)) in
                          let uu____4847 = mapM fa args in
                          bind uu____4847
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____4907 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____4907 with
                      | (bs1,t') ->
                          let uu____4916 =
                            let uu____4919 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____4919 t' in
                          bind uu____4916
                            (fun t''  ->
                               let uu____4923 =
                                 let uu____4924 =
                                   let uu____4941 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____4942 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____4941, uu____4942, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____4924 in
                               ret uu____4923))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____4963 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___174_4970 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___174_4970.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___174_4970.FStar_Syntax_Syntax.vars)
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
            let uu____5004 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____5004 with
            | (t1,lcomp,g) ->
                let uu____5016 =
                  (let uu____5019 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____5019) ||
                    (let uu____5021 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____5021) in
                if uu____5016
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____5031 = new_uvar "pointwise_rec" env typ in
                     bind uu____5031
                       (fun ut  ->
                          log ps
                            (fun uu____5042  ->
                               let uu____5043 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____5044 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5043 uu____5044);
                          (let uu____5045 =
                             let uu____5048 =
                               let uu____5049 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____5049 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5048 opts in
                           bind uu____5045
                             (fun uu____5052  ->
                                let uu____5053 =
                                  bind tau
                                    (fun uu____5059  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____5065  ->
                                            let uu____5066 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____5067 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5066 uu____5067);
                                       ret ut1) in
                                focus uu____5053))) in
                   let uu____5068 = trytac' rewrite_eq in
                   bind uu____5068
                     (fun x  ->
                        match x with
                        | FStar_Util.Inl "SKIP" -> ret t1
                        | FStar_Util.Inl e -> fail e
                        | FStar_Util.Inr x1 -> ret x1))
let pointwise:
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____5112 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5112 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5149  ->
                     let uu____5150 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5150);
                bind dismiss_all
                  (fun uu____5153  ->
                     let uu____5154 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5154
                       (fun gt'  ->
                          log ps
                            (fun uu____5164  ->
                               let uu____5165 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5165);
                          (let uu____5166 = push_goals gs in
                           bind uu____5166
                             (fun uu____5170  ->
                                add_goals
                                  [(let uu___176_5172 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___176_5172.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___176_5172.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___176_5172.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___176_5172.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5192 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5192 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5204 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5204 with
            | (hd1,args) ->
                let uu____5237 =
                  let uu____5250 =
                    let uu____5251 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5251.FStar_Syntax_Syntax.n in
                  (uu____5250, args) in
                (match uu____5237 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5265::(l,uu____5267)::(r,uu____5269)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5316 =
                       let uu____5317 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5317 in
                     if uu____5316
                     then
                       let uu____5320 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____5321 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5320 uu____5321
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5324) ->
                     let uu____5341 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5341))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5349 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5349
         (fun u  ->
            let g' =
              let uu___177_5356 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___177_5356.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___177_5356.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___177_5356.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___177_5356.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5359  ->
                 let uu____5360 =
                   let uu____5363 =
                     let uu____5364 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5364
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5363
                     g.FStar_Tactics_Types.opts in
                 bind uu____5360
                   (fun uu____5367  ->
                      let uu____5368 = add_goals [g'] in
                      bind uu____5368 (fun uu____5372  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___178_5389 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___178_5389.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___178_5389.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___178_5389.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___178_5389.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___178_5389.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___178_5389.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___178_5389.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___178_5389.FStar_Tactics_Types.entry_range)
              })
       | uu____5390 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___179_5405 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___179_5405.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___179_5405.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___179_5405.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___179_5405.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___179_5405.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___179_5405.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___179_5405.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___179_5405.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5412 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5431 =
      bind cur_goal
        (fun g  ->
           let uu____5445 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5445
             (fun uu____5481  ->
                match uu____5481 with
                | (t1,typ,guard) ->
                    let uu____5497 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5497 with
                     | (hd1,args) ->
                         let uu____5540 =
                           let uu____5553 =
                             let uu____5554 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5554.FStar_Syntax_Syntax.n in
                           (uu____5553, args) in
                         (match uu____5540 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5573)::(q,uu____5575)::[]) when
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
                                let uu___180_5613 = g in
                                let uu____5614 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5614;
                                  FStar_Tactics_Types.witness =
                                    (uu___180_5613.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___180_5613.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___180_5613.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___180_5613.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___181_5616 = g in
                                let uu____5617 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5617;
                                  FStar_Tactics_Types.witness =
                                    (uu___181_5616.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___181_5616.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___181_5616.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___181_5616.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5624  ->
                                   let uu____5625 = add_goals [g1; g2] in
                                   bind uu____5625
                                     (fun uu____5634  ->
                                        let uu____5635 =
                                          let uu____5640 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5641 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5640, uu____5641) in
                                        ret uu____5635))
                          | uu____5646 ->
                              let uu____5659 =
                                FStar_TypeChecker_Normalize.term_to_string
                                  g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5659)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5431
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5698 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5698);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___182_5705 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___182_5705.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___182_5705.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___182_5705.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___182_5705.FStar_Tactics_Types.is_guard)
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
      let uu____5743 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____5751 = __tc env tm in
             bind uu____5751
               (fun uu____5771  ->
                  match uu____5771 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____5743
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5804 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5810 =
              let uu____5811 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5811 in
            new_uvar "uvar_env.2" env uu____5810 in
      bind uu____5804
        (fun typ  ->
           let uu____5823 = new_uvar "uvar_env" env typ in
           bind uu____5823 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____5836 =
      bind cur_goal
        (fun goal  ->
           let uu____5842 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____5842
             (fun uu____5862  ->
                match uu____5862 with
                | (t1,typ,guard) ->
                    let uu____5874 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____5874
                      (fun uu____5879  ->
                         let uu____5880 =
                           let uu____5883 =
                             let uu___183_5884 = goal in
                             let uu____5885 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____5886 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___183_5884.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____5885;
                               FStar_Tactics_Types.goal_ty = uu____5886;
                               FStar_Tactics_Types.opts =
                                 (uu___183_5884.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____5883] in
                         add_goals uu____5880))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____5836
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5906 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5906)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5926  ->
             let uu____5927 = FStar_Options.unsafe_tactic_exec () in
             if uu____5927
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5933  -> fun uu____5934  -> false) in
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
      let uu____5956 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5956 with
      | (u,uu____5974,g_u) ->
          let g =
            let uu____5989 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5989;
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
      let uu____6006 = goal_of_goal_ty env typ in
      match uu____6006 with
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
              FStar_Tactics_Types.psc = FStar_TypeChecker_Normalize.null_psc;
              FStar_Tactics_Types.entry_range = FStar_Range.dummyRange
            } in
          (ps, (g.FStar_Tactics_Types.witness))