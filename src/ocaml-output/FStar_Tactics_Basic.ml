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
let tts:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  FStar_TypeChecker_Normalize.term_to_string
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
  'Auu____79 .
    'Auu____79 tac ->
      FStar_Tactics_Types.proofstate ->
        'Auu____79 FStar_Tactics_Result.__result
  = fun t  -> fun p  -> t.tac_f p
let ret: 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p))
let bind: 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____140 = run t1 p in
           match uu____140 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____147 = t2 a in run uu____147 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: FStar_Tactics_Types.goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____158 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____158
        (FStar_Syntax_Print.binders_to_string ", ") in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
    let uu____161 = tts g.FStar_Tactics_Types.context w in
    let uu____162 = tts g.FStar_Tactics_Types.context t in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____161 uu____162
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____172 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____172
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____182 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____182
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____195 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____195
let comp_to_typ: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____200) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____210) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: FStar_Tactics_Types.goal -> Prims.bool =
  fun g  ->
    let uu____223 =
      let uu____228 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty in
      FStar_Syntax_Util.un_squash uu____228 in
    match uu____223 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____234 -> false
let dump_goal:
  'Auu____242 . 'Auu____242 -> FStar_Tactics_Types.goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____252 = goal_to_string goal in tacprint uu____252
let dump_cur: FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____260 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____264 = FStar_List.hd ps.FStar_Tactics_Types.goals in
            dump_goal ps uu____264))
let ps_to_string:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu____271  ->
    match uu____271 with
    | (msg,ps) ->
        let uu____278 =
          let uu____281 =
            let uu____282 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____282 msg in
          let uu____283 =
            let uu____286 =
              let uu____287 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range in
              FStar_Util.format1 "Position: %s\n" uu____287 in
            let uu____288 =
              let uu____291 =
                let uu____292 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals) in
                let uu____293 =
                  let uu____294 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals in
                  FStar_String.concat "\n" uu____294 in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____292
                  uu____293 in
              let uu____297 =
                let uu____300 =
                  let uu____301 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals) in
                  let uu____302 =
                    let uu____303 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals in
                    FStar_String.concat "\n" uu____303 in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____301
                    uu____302 in
                [uu____300] in
              uu____291 :: uu____297 in
            uu____286 :: uu____288 in
          uu____281 :: uu____283 in
        FStar_String.concat "" uu____278
let goal_to_json: FStar_Tactics_Types.goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____310 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____310 FStar_Syntax_Print.binders_to_json in
    let uu____311 =
      let uu____318 =
        let uu____325 =
          let uu____330 =
            let uu____331 =
              let uu____338 =
                let uu____343 =
                  let uu____344 =
                    tts g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness in
                  FStar_Util.JsonStr uu____344 in
                ("witness", uu____343) in
              let uu____345 =
                let uu____352 =
                  let uu____357 =
                    let uu____358 =
                      tts g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty in
                    FStar_Util.JsonStr uu____358 in
                  ("type", uu____357) in
                [uu____352] in
              uu____338 :: uu____345 in
            FStar_Util.JsonAssoc uu____331 in
          ("goal", uu____330) in
        [uu____325] in
      ("hyps", g_binders) :: uu____318 in
    FStar_Util.JsonAssoc uu____311
let ps_to_json:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____389  ->
    match uu____389 with
    | (msg,ps) ->
        let uu____396 =
          let uu____403 =
            let uu____410 =
              let uu____415 =
                let uu____416 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals in
                FStar_Util.JsonList uu____416 in
              ("goals", uu____415) in
            let uu____419 =
              let uu____426 =
                let uu____431 =
                  let uu____432 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals in
                  FStar_Util.JsonList uu____432 in
                ("smt-goals", uu____431) in
              [uu____426] in
            uu____410 :: uu____419 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____403 in
        FStar_Util.JsonAssoc uu____396
let dump_proofstate:
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____459  ->
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
         (let uu____480 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_cur uu____480 msg);
         FStar_Tactics_Result.Success ((), ps))
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc in
         (let uu____496 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_proofstate uu____496 msg);
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
      let uu____525 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____525 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____579 =
              let uu____582 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____582 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____579);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'Auu____667 . Prims.string -> 'Auu____667 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____678 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____678
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____683 . Prims.string -> Prims.string -> 'Auu____683 tac =
  fun msg  ->
    fun x  -> let uu____694 = FStar_Util.format1 msg x in fail uu____694
let fail2:
  'Auu____699 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____699 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____714 = FStar_Util.format2 msg x y in fail uu____714
let fail3:
  'Auu____720 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____720 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____739 = FStar_Util.format3 msg x y z in fail uu____739
let trytac': 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____769 = run t ps in
         match uu____769 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____790) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____815 = trytac' t in
    bind uu____815
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____842 -> ret FStar_Pervasives_Native.None)
let wrap_err: 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____868 = run t ps in
           match uu____868 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____885  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____900 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____912 =
         let uu___283_913 = p in
         let uu____914 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___283_913.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___283_913.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___283_913.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____914;
           FStar_Tactics_Types.smt_goals =
             (uu___283_913.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___283_913.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___283_913.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___283_913.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___283_913.FStar_Tactics_Types.entry_range)
         } in
       set uu____912)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____927 = trysolve goal solution in
      if uu____927
      then dismiss
      else
        (let uu____931 =
           let uu____932 = tts goal.FStar_Tactics_Types.context solution in
           let uu____933 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____934 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____932 uu____933
             uu____934 in
         fail uu____931)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___284_941 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___284_941.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___284_941.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___284_941.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___284_941.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___284_941.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___284_941.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___284_941.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___284_941.FStar_Tactics_Types.entry_range)
          }))
let nwarn: Prims.int FStar_ST.ref = FStar_Util.mk_ref (Prims.parse_int "0")
let check_valid_goal: FStar_Tactics_Types.goal -> Prims.unit =
  fun g  ->
    let b = true in
    let env = g.FStar_Tactics_Types.context in
    let b1 =
      b && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.witness) in
    let b2 =
      b1 && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.goal_ty) in
    let rec aux b3 e =
      let uu____965 = FStar_TypeChecker_Env.pop_bv e in
      match uu____965 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____983 =
      (let uu____986 = aux b2 env in Prims.op_Negation uu____986) &&
        (let uu____988 = FStar_ST.op_Bang nwarn in
         uu____988 < (Prims.parse_int "5")) in
    if uu____983
    then
      ((let uu____1036 =
          let uu____1041 =
            let uu____1042 = goal_to_string g in
            FStar_Util.format1
              "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
              uu____1042 in
          (FStar_Errors.Warning_IllFormedGoal, uu____1041) in
        FStar_Errors.log_issue
          (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____1036);
       (let uu____1043 =
          let uu____1044 = FStar_ST.op_Bang nwarn in
          uu____1044 + (Prims.parse_int "1") in
        FStar_ST.op_Colon_Equals nwarn uu____1043))
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___285_1155 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___285_1155.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___285_1155.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___285_1155.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___285_1155.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___285_1155.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___285_1155.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___285_1155.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___285_1155.FStar_Tactics_Types.entry_range)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___286_1173 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___286_1173.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___286_1173.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___286_1173.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___286_1173.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___286_1173.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___286_1173.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___286_1173.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___286_1173.FStar_Tactics_Types.entry_range)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___287_1191 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___287_1191.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___287_1191.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___287_1191.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___287_1191.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___287_1191.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___287_1191.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___287_1191.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___287_1191.FStar_Tactics_Types.entry_range)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___288_1209 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___288_1209.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___288_1209.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___288_1209.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___288_1209.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___288_1209.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___288_1209.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___288_1209.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___288_1209.FStar_Tactics_Types.entry_range)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1218  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___289_1230 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___289_1230.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___289_1230.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___289_1230.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___289_1230.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___289_1230.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___289_1230.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___289_1230.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___289_1230.FStar_Tactics_Types.entry_range)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1256 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1256 with
        | (u,uu____1272,g_u) ->
            let uu____1286 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1286 (fun uu____1290  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1294 = FStar_Syntax_Util.un_squash t in
    match uu____1294 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1304 =
          let uu____1305 = FStar_Syntax_Subst.compress t' in
          uu____1305.FStar_Syntax_Syntax.n in
        (match uu____1304 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1309 -> false)
    | uu____1310 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1318 = FStar_Syntax_Util.un_squash t in
    match uu____1318 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1328 =
          let uu____1329 = FStar_Syntax_Subst.compress t' in
          uu____1329.FStar_Syntax_Syntax.n in
        (match uu____1328 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1333 -> false)
    | uu____1334 -> false
let cur_goal: FStar_Tactics_Types.goal tac =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let is_guard: Prims.bool tac =
  bind cur_goal (fun g  -> ret g.FStar_Tactics_Types.is_guard)
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
          let uu____1372 = new_uvar reason env typ in
          bind uu____1372
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
             let uu____1428 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1428
           with | e1 -> fail "not typeable")
let must_trivial: env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1476 =
          let uu____1477 =
            let uu____1478 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1478 in
          Prims.op_Negation uu____1477 in
        if uu____1476 then fail "got non-trivial guard" else ret ()
      with | uu____1487 -> fail "got non-trivial guard"
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1495 =
      bind cur_goal
        (fun goal  ->
           let uu____1501 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1501
             (fun uu____1521  ->
                match uu____1521 with
                | (t1,typ,guard) ->
                    let uu____1533 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____1533 (fun uu____1537  -> ret typ))) in
    FStar_All.pipe_left (wrap_err "tc") uu____1495
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1558 = mk_irrelevant_goal reason env phi opts in
          bind uu____1558 (fun goal  -> add_goals [goal])
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
       let uu____1578 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1578
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1582 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1582))
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
          let uu____1599 =
            let uu____1600 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1600.FStar_TypeChecker_Env.guard_f in
          match uu____1599 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1604 = istrivial e f in
              if uu____1604
              then ret ()
              else
                (let uu____1608 = mk_irrelevant_goal reason e f opts in
                 bind uu____1608
                   (fun goal  ->
                      let goal1 =
                        let uu___294_1615 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___294_1615.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___294_1615.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___294_1615.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___294_1615.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard = true
                        } in
                      push_goals [goal1]))
let goal_from_guard:
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t ->
        FStar_Options.optionstate ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option tac
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____1636 =
            let uu____1637 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1637.FStar_TypeChecker_Env.guard_f in
          match uu____1636 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1645 = istrivial e f in
              if uu____1645
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1653 = mk_irrelevant_goal reason e f opts in
                 bind uu____1653
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___295_1663 = goal in
                            {
                              FStar_Tactics_Types.context =
                                (uu___295_1663.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___295_1663.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___295_1663.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___295_1663.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1669 = is_irrelevant g in
       if uu____1669
       then bind dismiss (fun uu____1673  -> add_smt_goals [g])
       else
         (let uu____1675 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1675))
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
             let uu____1716 =
               try
                 let uu____1750 =
                   let uu____1759 = FStar_BigInt.to_int_fs n1 in
                   FStar_List.splitAt uu____1759 p.FStar_Tactics_Types.goals in
                 ret uu____1750
               with | uu____1781 -> fail "divide: not enough goals" in
             bind uu____1716
               (fun uu____1808  ->
                  match uu____1808 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___296_1834 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___296_1834.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___296_1834.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___296_1834.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___296_1834.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___296_1834.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___296_1834.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___296_1834.FStar_Tactics_Types.entry_range)
                        } in
                      let rp =
                        let uu___297_1836 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___297_1836.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___297_1836.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___297_1836.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___297_1836.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___297_1836.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___297_1836.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___297_1836.FStar_Tactics_Types.entry_range)
                        } in
                      let uu____1837 = set lp in
                      bind uu____1837
                        (fun uu____1845  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1859 = set rp in
                                     bind uu____1859
                                       (fun uu____1867  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___298_1883 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___298_1883.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___298_1883.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___298_1883.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___298_1883.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___298_1883.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___298_1883.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___298_1883.FStar_Tactics_Types.entry_range)
                                                      } in
                                                    let uu____1884 = set p' in
                                                    bind uu____1884
                                                      (fun uu____1892  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1910 = divide FStar_BigInt.one f idtac in
    bind uu____1910
      (fun uu____1923  -> match uu____1923 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1957::uu____1958 ->
             let uu____1961 =
               let uu____1970 = map tau in
               divide FStar_BigInt.one tau uu____1970 in
             bind uu____1961
               (fun uu____1988  ->
                  match uu____1988 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____2025 =
        bind t1
          (fun uu____2030  ->
             let uu____2031 = map t2 in
             bind uu____2031 (fun uu____2039  -> ret ())) in
      focus uu____2025
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____2050 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____2050 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2065 =
             let uu____2066 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____2066 in
           if uu____2065
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____2072 = new_uvar "intro" env' typ' in
              bind uu____2072
                (fun u  ->
                   let uu____2079 =
                     let uu____2080 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____2080 in
                   if uu____2079
                   then
                     let uu____2083 =
                       let uu____2086 =
                         let uu___301_2087 = goal in
                         let uu____2088 = bnorm env' u in
                         let uu____2089 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2088;
                           FStar_Tactics_Types.goal_ty = uu____2089;
                           FStar_Tactics_Types.opts =
                             (uu___301_2087.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___301_2087.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____2086 in
                     bind uu____2083 (fun uu____2091  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2097 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____2097)
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
       (let uu____2118 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____2118 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2137 =
              let uu____2138 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____2138 in
            if uu____2137
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____2154 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____2154; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____2156 =
                 let uu____2159 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____2159 in
               bind uu____2156
                 (fun u  ->
                    let lb =
                      let uu____2175 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2175 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2179 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2179 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2216 =
                            let uu____2219 =
                              let uu___302_2220 = goal in
                              let uu____2221 = bnorm env' u in
                              let uu____2222 =
                                let uu____2223 = comp_to_typ c in
                                bnorm env' uu____2223 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2221;
                                FStar_Tactics_Types.goal_ty = uu____2222;
                                FStar_Tactics_Types.opts =
                                  (uu___302_2220.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___302_2220.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2219 in
                          bind uu____2216
                            (fun uu____2230  ->
                               let uu____2231 =
                                 let uu____2236 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2236, b) in
                               ret uu____2231)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2250 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2250))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2274 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2274 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___303_2281 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___303_2281.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___303_2281.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___303_2281.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2299 =
          bind get
            (fun ps  ->
               let uu____2305 = __tc e t in
               bind uu____2305
                 (fun uu____2327  ->
                    match uu____2327 with
                    | (t1,uu____2337,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2343 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2343 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2299
let refine_intro: Prims.unit tac =
  let uu____2353 =
    bind cur_goal
      (fun g  ->
         let uu____2360 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
         match uu____2360 with
         | (uu____2373,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___304_2398 = g in
               {
                 FStar_Tactics_Types.context =
                   (uu___304_2398.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___304_2398.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___304_2398.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___304_2398.FStar_Tactics_Types.is_guard)
               } in
             let uu____2399 =
               let uu____2404 =
                 let uu____2409 =
                   let uu____2410 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2410] in
                 FStar_Syntax_Subst.open_term uu____2409 phi in
               match uu____2404 with
               | (bvs,phi1) ->
                   let uu____2417 =
                     let uu____2418 = FStar_List.hd bvs in
                     FStar_Pervasives_Native.fst uu____2418 in
                   (uu____2417, phi1) in
             (match uu____2399 with
              | (bv1,phi1) ->
                  let uu____2431 =
                    let uu____2434 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1 in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2434
                      g.FStar_Tactics_Types.opts in
                  bind uu____2431
                    (fun g2  ->
                       bind dismiss (fun uu____2438  -> add_goals [g1; g2])))) in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2353
let __exact_now:
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun t  ->
        bind cur_goal
          (fun goal  ->
             let env =
               if set_expected_typ1
               then
                 FStar_TypeChecker_Env.set_expected_typ
                   goal.FStar_Tactics_Types.context
                   goal.FStar_Tactics_Types.goal_ty
               else goal.FStar_Tactics_Types.context in
             let uu____2462 = __tc env t in
             bind uu____2462
               (fun uu____2482  ->
                  match uu____2482 with
                  | (t1,typ,guard) ->
                      let uu____2494 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts in
                      bind uu____2494
                        (fun uu____2501  ->
                           mlog
                             (fun uu____2505  ->
                                let uu____2506 =
                                  tts goal.FStar_Tactics_Types.context typ in
                                let uu____2507 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2506
                                  uu____2507)
                             (fun uu____2510  ->
                                let uu____2511 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty in
                                if uu____2511
                                then solve goal t1
                                else
                                  (let uu____2515 =
                                     tts goal.FStar_Tactics_Types.context t1 in
                                   let uu____2516 =
                                     tts goal.FStar_Tactics_Types.context typ in
                                   let uu____2517 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty in
                                   fail3
                                     "%s : %s does not exactly solve the goal %s"
                                     uu____2515 uu____2516 uu____2517)))))
let t_exact:
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2531 =
          mlog
            (fun uu____2536  ->
               let uu____2537 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "exact: tm = %s\n" uu____2537)
            (fun uu____2540  ->
               let uu____2541 =
                 let uu____2548 =
                   __exact_now set_expected_typ1 force_guard tm in
                 trytac' uu____2548 in
               bind uu____2541
                 (fun uu___278_2557  ->
                    match uu___278_2557 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2566 =
                          let uu____2573 =
                            let uu____2576 =
                              norm [FStar_Syntax_Embeddings.Delta] in
                            bind uu____2576
                              (fun uu____2580  ->
                                 bind refine_intro
                                   (fun uu____2582  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm)) in
                          trytac' uu____2573 in
                        bind uu____2566
                          (fun uu___277_2589  ->
                             match uu___277_2589 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2597 -> fail e))) in
        FStar_All.pipe_left (wrap_err "exact") uu____2531
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2612 =
             let uu____2619 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2619 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2612 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____2679 = f x in
          bind uu____2679
            (fun y  ->
               let uu____2687 = mapM f xs in
               bind uu____2687 (fun ys  -> ret (y :: ys)))
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2705 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2722 =
               let uu____2727 = t_exact false true tm in trytac uu____2727 in
             bind uu____2722
               (fun uu___279_2734  ->
                  match uu___279_2734 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2740 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2740 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2772  ->
                                let uu____2773 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2773)
                             (fun uu____2776  ->
                                let uu____2777 =
                                  let uu____2778 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2778 in
                                if uu____2777
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2782 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2782
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2802 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2802 in
                                        let uu____2803 =
                                          __apply uopt tm' typ' in
                                        bind uu____2803
                                          (fun uu____2811  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2813 =
                                               let uu____2814 =
                                                 let uu____2817 =
                                                   let uu____2818 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2818 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2817 in
                                               uu____2814.FStar_Syntax_Syntax.n in
                                             match uu____2813 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2846) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2874 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2874
                                                      then ret ()
                                                      else
                                                        (let uu____2878 =
                                                           let uu____2881 =
                                                             let uu___305_2882
                                                               = goal in
                                                             let uu____2883 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2884 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___305_2882.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2883;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2884;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___305_2882.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2881] in
                                                         add_goals uu____2878))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2930 =
        mlog
          (fun uu____2935  ->
             let uu____2936 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2936)
          (fun uu____2938  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2942 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2942
                    (fun uu____2963  ->
                       match uu____2963 with
                       | (tm1,typ,guard) ->
                           let uu____2975 =
                             let uu____2978 =
                               let uu____2981 = __apply uopt tm1 typ in
                               bind uu____2981
                                 (fun uu____2985  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2978 in
                           let uu____2986 =
                             let uu____2989 =
                               tts goal.FStar_Tactics_Types.context tm1 in
                             let uu____2990 =
                               tts goal.FStar_Tactics_Types.context typ in
                             let uu____2991 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2989 uu____2990 uu____2991 in
                           try_unif uu____2975 uu____2986))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2930
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____3003 =
      let uu____3006 =
        mlog
          (fun uu____3011  ->
             let uu____3012 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3012)
          (fun uu____3015  ->
             let is_unit_t t =
               let uu____3020 =
                 let uu____3021 = FStar_Syntax_Subst.compress t in
                 uu____3021.FStar_Syntax_Syntax.n in
               match uu____3020 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3025 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____3029 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____3029
                    (fun uu____3051  ->
                       match uu____3051 with
                       | (tm1,t,guard) ->
                           let uu____3063 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____3063 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3093 =
                                     FStar_List.fold_left
                                       (fun uu____3139  ->
                                          fun uu____3140  ->
                                            match (uu____3139, uu____3140)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____3243 =
                                                  is_unit_t b_t in
                                                if uu____3243
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3281 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____3281 with
                                                   | (u,uu____3311,g_u) ->
                                                       let uu____3325 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____3325,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____3093 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3395 =
                                         let uu____3404 =
                                           let uu____3413 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3413.FStar_Syntax_Syntax.effect_args in
                                         match uu____3404 with
                                         | pre::post::uu____3424 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3465 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3395 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3497 =
                                                let uu____3506 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3506] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3497 in
                                            let uu____3507 =
                                              let uu____3508 =
                                                let uu____3509 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3509
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3508 in
                                            if uu____3507
                                            then
                                              let uu____3512 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3513 =
                                                let uu____3514 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3514 in
                                              let uu____3515 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3512 uu____3513
                                                uu____3515
                                            else
                                              (let solution =
                                                 let uu____3518 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3518 in
                                               let uu____3519 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3519
                                                 (fun uu____3524  ->
                                                    let uu____3525 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit in
                                                    bind uu____3525
                                                      (fun uu____3533  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3544 =
                                                               let uu____3551
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3551 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3544 in
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
                                                           let uu____3592 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3592
                                                           with
                                                           | (hd1,uu____3608)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3630)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3655
                                                                    -> false) in
                                                         let uu____3656 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3728
                                                                    ->
                                                                   match uu____3728
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3756)
                                                                    ->
                                                                    let uu____3757
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____3757
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3783)
                                                                    ->
                                                                    let uu____3804
                                                                    =
                                                                    let uu____3805
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3805.FStar_Syntax_Syntax.n in
                                                                    (match uu____3804
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3818
                                                                    ->
                                                                    let uu____3835
                                                                    =
                                                                    let uu____3844
                                                                    =
                                                                    let uu____3847
                                                                    =
                                                                    let uu___308_3848
                                                                    = goal in
                                                                    let uu____3849
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3850
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___308_3848.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3849;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3850;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___308_3848.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___308_3848.FStar_Tactics_Types.is_guard)
                                                                    } in
                                                                    [uu____3847] in
                                                                    (uu____3844,
                                                                    []) in
                                                                    ret
                                                                    uu____3835
                                                                    | 
                                                                    uu____3863
                                                                    ->
                                                                    let term1
                                                                    =
                                                                    bnorm env
                                                                    term in
                                                                    let uu____3865
                                                                    =
                                                                    let uu____3872
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3872
                                                                    term1 in
                                                                    (match uu____3865
                                                                    with
                                                                    | 
                                                                    (uu____3883,uu____3884,g_typ)
                                                                    ->
                                                                    let uu____3886
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts in
                                                                    bind
                                                                    uu____3886
                                                                    (fun
                                                                    uu___280_3902
                                                                     ->
                                                                    match uu___280_3902
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    ret
                                                                    ([], [])
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g ->
                                                                    ret
                                                                    ([], [g]))))))) in
                                                         bind uu____3656
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3970
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3970 in
                                                              let smt_goals =
                                                                let uu____3992
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3992 in
                                                              let rec filter'
                                                                f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4048
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____4048
                                                                    then
                                                                    let uu____4051
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____4051
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                              let sub_goals1
                                                                =
                                                                filter'
                                                                  (fun g  ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4065
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____4065)
                                                                  sub_goals in
                                                              let uu____4066
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts in
                                                              bind uu____4066
                                                                (fun
                                                                   uu____4071
                                                                    ->
                                                                   let uu____4072
                                                                    =
                                                                    let uu____4075
                                                                    =
                                                                    let uu____4076
                                                                    =
                                                                    let uu____4077
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4077 in
                                                                    Prims.op_Negation
                                                                    uu____4076 in
                                                                    if
                                                                    uu____4075
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret () in
                                                                   bind
                                                                    uu____4072
                                                                    (fun
                                                                    uu____4083
                                                                     ->
                                                                    let uu____4084
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals in
                                                                    bind
                                                                    uu____4084
                                                                    (fun
                                                                    uu____4088
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))) in
      focus uu____3006 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3003
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4108 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____4108 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4118::(e1,uu____4120)::(e2,uu____4122)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4181 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4203 = destruct_eq' typ in
    match uu____4203 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4233 = FStar_Syntax_Util.un_squash typ in
        (match uu____4233 with
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
        let uu____4289 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____4289 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4337 = aux e' in
               FStar_Util.map_opt uu____4337
                 (fun uu____4361  ->
                    match uu____4361 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____4382 = aux e in
      FStar_Util.map_opt uu____4382
        (fun uu____4406  ->
           match uu____4406 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____4461 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____4461
            (fun uu____4485  ->
               match uu____4485 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___309_4502 = bv in
                     let uu____4503 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___309_4502.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___309_4502.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4503
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___310_4512 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___310_4512.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___310_4512.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4525 = h in
         match uu____4525 with
         | (bv,uu____4529) ->
             mlog
               (fun uu____4533  ->
                  let uu____4534 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4535 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4534
                    uu____4535)
               (fun uu____4538  ->
                  let uu____4539 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4539 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4568 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4568 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4583 =
                             let uu____4584 = FStar_Syntax_Subst.compress x in
                             uu____4584.FStar_Syntax_Syntax.n in
                           (match uu____4583 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___311_4597 = bv1 in
                                  let uu____4598 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___311_4597.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___311_4597.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4598
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4604 =
                                  let uu___312_4605 = goal in
                                  let uu____4606 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4607 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4608 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4606;
                                    FStar_Tactics_Types.witness = uu____4607;
                                    FStar_Tactics_Types.goal_ty = uu____4608;
                                    FStar_Tactics_Types.opts =
                                      (uu___312_4605.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___312_4605.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4604
                            | uu____4609 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4610 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4635 = b in
           match uu____4635 with
           | (bv,uu____4639) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___313_4643 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___313_4643.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___313_4643.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4647 =
                   let uu____4648 =
                     let uu____4655 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4655) in
                   FStar_Syntax_Syntax.NT uu____4648 in
                 [uu____4647] in
               let uu____4656 = subst_goal bv bv' s1 goal in
               (match uu____4656 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4675 = b in
         match uu____4675 with
         | (bv,uu____4679) ->
             let uu____4680 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4680 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4709 = FStar_Syntax_Util.type_u () in
                  (match uu____4709 with
                   | (ty,u) ->
                       let uu____4718 = new_uvar "binder_retype" e0 ty in
                       bind uu____4718
                         (fun t'  ->
                            let bv'' =
                              let uu___314_4728 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___314_4728.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___314_4728.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4732 =
                                let uu____4733 =
                                  let uu____4740 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4740) in
                                FStar_Syntax_Syntax.NT uu____4733 in
                              [uu____4732] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___315_4748 = b1 in
                                   let uu____4749 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___315_4748.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___315_4748.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4749
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4755  ->
                                 let uu____4756 =
                                   let uu____4759 =
                                     let uu____4762 =
                                       let uu___316_4763 = goal in
                                       let uu____4764 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4765 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4764;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4765;
                                         FStar_Tactics_Types.opts =
                                           (uu___316_4763.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___316_4763.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4762] in
                                   add_goals uu____4759 in
                                 bind uu____4756
                                   (fun uu____4768  ->
                                      let uu____4769 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4769
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4790 = b in
           match uu____4790 with
           | (bv,uu____4794) ->
               let uu____4795 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4795 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4827 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4827 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___317_4832 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___317_4832.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___317_4832.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___318_4836 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___318_4836.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___318_4836.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___318_4836.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___318_4836.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4842 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4842 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4864 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4864 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___319_4898 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___319_4898.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___319_4898.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4909 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4909 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4930 = FStar_Syntax_Print.bv_to_string x in
               let uu____4931 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4930 uu____4931
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4938 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4938 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4960 = FStar_Util.set_mem x fns_ty in
           if uu____4960
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4964 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4964
                (fun u  ->
                   let uu____4970 =
                     let uu____4971 = trysolve goal u in
                     Prims.op_Negation uu____4971 in
                   if uu____4970
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___320_4976 = goal in
                        let uu____4977 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4977;
                          FStar_Tactics_Types.goal_ty =
                            (uu___320_4976.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___320_4976.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___320_4976.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4979  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4990 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4990 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____5014  ->
                    let uu____5015 = clear b in
                    bind uu____5015
                      (fun uu____5019  ->
                         bind intro (fun uu____5021  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___321_5037 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___321_5037.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___321_5037.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___321_5037.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___321_5037.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5039  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___322_5055 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___322_5055.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___322_5055.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___322_5055.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___322_5055.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5057  -> add_goals [g']))
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
            let uu____5089 = FStar_Syntax_Subst.compress t in
            uu____5089.FStar_Syntax_Syntax.n in
          let uu____5092 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___324_5098 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___324_5098.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___324_5098.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____5092
            (fun t1  ->
               let tn1 =
                 let uu____5106 =
                   let uu____5107 = FStar_Syntax_Subst.compress t1 in
                   uu____5107.FStar_Syntax_Syntax.n in
                 match uu____5106 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____5139 = ff hd1 in
                     bind uu____5139
                       (fun hd2  ->
                          let fa uu____5159 =
                            match uu____5159 with
                            | (a,q) ->
                                let uu____5172 = ff a in
                                bind uu____5172 (fun a1  -> ret (a1, q)) in
                          let uu____5185 = mapM fa args in
                          bind uu____5185
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5245 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____5245 with
                      | (bs1,t') ->
                          let uu____5254 =
                            let uu____5257 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____5257 t' in
                          bind uu____5254
                            (fun t''  ->
                               let uu____5261 =
                                 let uu____5262 =
                                   let uu____5279 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____5280 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____5279, uu____5280, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____5262 in
                               ret uu____5261))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5301 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___323_5308 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___323_5308.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___323_5308.FStar_Syntax_Syntax.vars)
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
            let uu____5337 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____5337 with
            | (t1,lcomp,g) ->
                let uu____5349 =
                  (let uu____5352 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____5352) ||
                    (let uu____5354 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____5354) in
                if uu____5349
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____5364 = new_uvar "pointwise_rec" env typ in
                     bind uu____5364
                       (fun ut  ->
                          log ps
                            (fun uu____5375  ->
                               let uu____5376 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____5377 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5376 uu____5377);
                          (let uu____5378 =
                             let uu____5381 =
                               let uu____5382 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____5382 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5381 opts in
                           bind uu____5378
                             (fun uu____5385  ->
                                let uu____5386 =
                                  bind tau
                                    (fun uu____5392  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____5398  ->
                                            let uu____5399 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____5400 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5399 uu____5400);
                                       ret ut1) in
                                focus uu____5386))) in
                   let uu____5401 = trytac' rewrite_eq in
                   bind uu____5401
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
           let uu____5443 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5443 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5480  ->
                     let uu____5481 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5481);
                bind dismiss_all
                  (fun uu____5484  ->
                     let uu____5485 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5485
                       (fun gt'  ->
                          log ps
                            (fun uu____5495  ->
                               let uu____5496 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5496);
                          (let uu____5497 = push_goals gs in
                           bind uu____5497
                             (fun uu____5501  ->
                                add_goals
                                  [(let uu___325_5503 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___325_5503.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___325_5503.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___325_5503.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___325_5503.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5523 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5523 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5535 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5535 with
            | (hd1,args) ->
                let uu____5568 =
                  let uu____5581 =
                    let uu____5582 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5582.FStar_Syntax_Syntax.n in
                  (uu____5581, args) in
                (match uu____5568 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5596::(l,uu____5598)::(r,uu____5600)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5647 =
                       let uu____5648 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5648 in
                     if uu____5647
                     then
                       let uu____5651 = tts g.FStar_Tactics_Types.context l in
                       let uu____5652 = tts g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5651 uu____5652
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5655) ->
                     let uu____5672 = tts g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5672))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5680 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5680
         (fun u  ->
            let g' =
              let uu___326_5687 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___326_5687.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___326_5687.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___326_5687.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___326_5687.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5690  ->
                 let uu____5691 =
                   let uu____5694 =
                     let uu____5695 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5695
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5694
                     g.FStar_Tactics_Types.opts in
                 bind uu____5691
                   (fun uu____5698  ->
                      let uu____5699 = add_goals [g'] in
                      bind uu____5699 (fun uu____5703  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___327_5720 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___327_5720.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___327_5720.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___327_5720.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___327_5720.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___327_5720.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___327_5720.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___327_5720.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___327_5720.FStar_Tactics_Types.entry_range)
              })
       | uu____5721 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___328_5736 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___328_5736.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___328_5736.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___328_5736.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___328_5736.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___328_5736.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___328_5736.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___328_5736.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___328_5736.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5743 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5761 =
      bind cur_goal
        (fun g  ->
           let uu____5775 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5775
             (fun uu____5811  ->
                match uu____5811 with
                | (t1,typ,guard) ->
                    let uu____5827 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5827 with
                     | (hd1,args) ->
                         let uu____5870 =
                           let uu____5883 =
                             let uu____5884 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5884.FStar_Syntax_Syntax.n in
                           (uu____5883, args) in
                         (match uu____5870 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5903)::(q,uu____5905)::[]) when
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
                                let uu___329_5943 = g in
                                let uu____5944 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5944;
                                  FStar_Tactics_Types.witness =
                                    (uu___329_5943.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___329_5943.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___329_5943.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___329_5943.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___330_5946 = g in
                                let uu____5947 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5947;
                                  FStar_Tactics_Types.witness =
                                    (uu___330_5946.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___330_5946.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___330_5946.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___330_5946.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5954  ->
                                   let uu____5955 = add_goals [g1; g2] in
                                   bind uu____5955
                                     (fun uu____5964  ->
                                        let uu____5965 =
                                          let uu____5970 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5971 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5970, uu____5971) in
                                        ret uu____5965))
                          | uu____5976 ->
                              let uu____5989 =
                                tts g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5989)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5761
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6027 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____6027);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___331_6034 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___331_6034.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___331_6034.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___331_6034.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___331_6034.FStar_Tactics_Types.is_guard)
                 } in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
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
      let uu____6070 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____6078 = __tc env tm in
             bind uu____6078
               (fun uu____6098  ->
                  match uu____6098 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____6070
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____6129 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6135 =
              let uu____6136 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6136 in
            new_uvar "uvar_env.2" env uu____6135 in
      bind uu____6129
        (fun typ  ->
           let uu____6148 = new_uvar "uvar_env" env typ in
           bind uu____6148 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____6160 =
      bind cur_goal
        (fun goal  ->
           let uu____6166 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____6166
             (fun uu____6186  ->
                match uu____6186 with
                | (t1,typ,guard) ->
                    let uu____6198 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____6198
                      (fun uu____6203  ->
                         let uu____6204 =
                           let uu____6207 =
                             let uu___332_6208 = goal in
                             let uu____6209 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____6210 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___332_6208.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6209;
                               FStar_Tactics_Types.goal_ty = uu____6210;
                               FStar_Tactics_Types.opts =
                                 (uu___332_6208.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____6207] in
                         add_goals uu____6204))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6160
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6228 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____6228)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6245  ->
             let uu____6246 = FStar_Options.unsafe_tactic_exec () in
             if uu____6246
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6252  -> fun uu____6253  -> false) in
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
      let uu____6273 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____6273 with
      | (u,uu____6291,g_u) ->
          let g =
            let uu____6306 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6306;
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
      let uu____6321 = goal_of_goal_ty env typ in
      match uu____6321 with
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