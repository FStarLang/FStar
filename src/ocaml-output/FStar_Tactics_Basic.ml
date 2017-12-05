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
        let debug_on uu____898 =
          let uu____899 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck" in
          () in
        let debug_off uu____903 =
          let uu____904 = FStar_Options.set_options FStar_Options.Reset "" in
          () in
        (let uu____906 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346") in
         if uu____906
         then
           (debug_on ();
            (let uu____908 = FStar_Syntax_Print.term_to_string t1 in
             let uu____909 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____908
               uu____909))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2 in
           debug_off (); res
         with | uu____900_921 -> (debug_off (); false))
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____934 =
         let uu___285_935 = p in
         let uu____936 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___285_935.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___285_935.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___285_935.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____936;
           FStar_Tactics_Types.smt_goals =
             (uu___285_935.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___285_935.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___285_935.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___285_935.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___285_935.FStar_Tactics_Types.entry_range)
         } in
       set uu____934)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____949 = trysolve goal solution in
      if uu____949
      then dismiss
      else
        (let uu____953 =
           let uu____954 = tts goal.FStar_Tactics_Types.context solution in
           let uu____955 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____956 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____954 uu____955
             uu____956 in
         fail uu____953)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___286_963 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___286_963.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___286_963.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___286_963.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___286_963.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___286_963.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___286_963.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___286_963.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___286_963.FStar_Tactics_Types.entry_range)
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
      let uu____987 = FStar_TypeChecker_Env.pop_bv e in
      match uu____987 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____1005 =
      (let uu____1008 = aux b2 env in Prims.op_Negation uu____1008) &&
        (let uu____1010 = FStar_ST.op_Bang nwarn in
         uu____1010 < (Prims.parse_int "5")) in
    if uu____1005
    then
      ((let uu____1058 =
          let uu____1059 = goal_to_string g in
          FStar_Util.format1
            "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
            uu____1059 in
        FStar_Errors.warn
          (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____1058);
       (let uu____1060 =
          let uu____1061 = FStar_ST.op_Bang nwarn in
          uu____1061 + (Prims.parse_int "1") in
        FStar_ST.op_Colon_Equals nwarn uu____1060))
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___287_1172 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___287_1172.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___287_1172.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___287_1172.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___287_1172.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___287_1172.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___287_1172.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___287_1172.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___287_1172.FStar_Tactics_Types.entry_range)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___288_1190 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___288_1190.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___288_1190.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___288_1190.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___288_1190.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___288_1190.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___288_1190.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___288_1190.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___288_1190.FStar_Tactics_Types.entry_range)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___289_1208 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___289_1208.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___289_1208.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___289_1208.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___289_1208.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___289_1208.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___289_1208.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___289_1208.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___289_1208.FStar_Tactics_Types.entry_range)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___290_1226 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___290_1226.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___290_1226.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___290_1226.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___290_1226.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___290_1226.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___290_1226.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___290_1226.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___290_1226.FStar_Tactics_Types.entry_range)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1235  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___291_1247 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___291_1247.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___291_1247.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___291_1247.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___291_1247.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___291_1247.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___291_1247.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___291_1247.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___291_1247.FStar_Tactics_Types.entry_range)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1273 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1273 with
        | (u,uu____1289,g_u) ->
            let uu____1303 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1303 (fun uu____1307  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1311 = FStar_Syntax_Util.un_squash t in
    match uu____1311 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1321 =
          let uu____1322 = FStar_Syntax_Subst.compress t' in
          uu____1322.FStar_Syntax_Syntax.n in
        (match uu____1321 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1326 -> false)
    | uu____1327 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1335 = FStar_Syntax_Util.un_squash t in
    match uu____1335 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1345 =
          let uu____1346 = FStar_Syntax_Subst.compress t' in
          uu____1346.FStar_Syntax_Syntax.n in
        (match uu____1345 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1350 -> false)
    | uu____1351 -> false
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
          let typ =
            let uu____1389 = env.FStar_TypeChecker_Env.universe_of env phi in
            FStar_Syntax_Util.mk_squash uu____1389 phi in
          let uu____1390 = new_uvar reason env typ in
          bind uu____1390
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
             let uu____1446 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1446
           with | e1 -> fail "not typeable")
let must_trivial: env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1494 =
          let uu____1495 =
            let uu____1496 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1496 in
          Prims.op_Negation uu____1495 in
        if uu____1494 then fail "got non-trivial guard" else ret ()
      with | uu____1505 -> fail "got non-trivial guard"
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1513 =
      bind cur_goal
        (fun goal  ->
           let uu____1519 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1519
             (fun uu____1539  ->
                match uu____1539 with
                | (t1,typ,guard) ->
                    let uu____1551 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____1551 (fun uu____1555  -> ret typ))) in
    FStar_All.pipe_left (wrap_err "tc") uu____1513
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1576 = mk_irrelevant_goal reason env phi opts in
          bind uu____1576 (fun goal  -> add_goals [goal])
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
       let uu____1596 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1596
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1600 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1600))
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
          let uu____1617 =
            let uu____1618 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1618.FStar_TypeChecker_Env.guard_f in
          match uu____1617 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1622 = istrivial e f in
              if uu____1622
              then ret ()
              else
                (let uu____1626 = mk_irrelevant_goal reason e f opts in
                 bind uu____1626
                   (fun goal  ->
                      let goal1 =
                        let uu___296_1633 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___296_1633.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___296_1633.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___296_1633.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___296_1633.FStar_Tactics_Types.opts);
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
          let uu____1654 =
            let uu____1655 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1655.FStar_TypeChecker_Env.guard_f in
          match uu____1654 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1663 = istrivial e f in
              if uu____1663
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1671 = mk_irrelevant_goal reason e f opts in
                 bind uu____1671
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___297_1681 = goal in
                            {
                              FStar_Tactics_Types.context =
                                (uu___297_1681.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___297_1681.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___297_1681.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___297_1681.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1687 = is_irrelevant g in
       if uu____1687
       then bind dismiss (fun uu____1691  -> add_smt_goals [g])
       else
         (let uu____1693 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1693))
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
             let uu____1734 =
               try
                 let uu____1768 =
                   let uu____1777 = FStar_BigInt.to_int_fs n1 in
                   FStar_List.splitAt uu____1777 p.FStar_Tactics_Types.goals in
                 ret uu____1768
               with | uu____1799 -> fail "divide: not enough goals" in
             bind uu____1734
               (fun uu____1826  ->
                  match uu____1826 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___298_1852 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___298_1852.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___298_1852.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___298_1852.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___298_1852.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___298_1852.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___298_1852.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___298_1852.FStar_Tactics_Types.entry_range)
                        } in
                      let rp =
                        let uu___299_1854 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___299_1854.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___299_1854.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___299_1854.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___299_1854.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___299_1854.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___299_1854.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___299_1854.FStar_Tactics_Types.entry_range)
                        } in
                      let uu____1855 = set lp in
                      bind uu____1855
                        (fun uu____1863  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1877 = set rp in
                                     bind uu____1877
                                       (fun uu____1885  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___300_1901 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___300_1901.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___300_1901.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___300_1901.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___300_1901.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___300_1901.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___300_1901.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___300_1901.FStar_Tactics_Types.entry_range)
                                                      } in
                                                    let uu____1902 = set p' in
                                                    bind uu____1902
                                                      (fun uu____1910  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1928 = divide FStar_BigInt.one f idtac in
    bind uu____1928
      (fun uu____1941  -> match uu____1941 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1975::uu____1976 ->
             let uu____1979 =
               let uu____1988 = map tau in
               divide FStar_BigInt.one tau uu____1988 in
             bind uu____1979
               (fun uu____2006  ->
                  match uu____2006 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____2043 =
        bind t1
          (fun uu____2048  ->
             let uu____2049 = map t2 in
             bind uu____2049 (fun uu____2057  -> ret ())) in
      focus uu____2043
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____2068 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____2068 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2083 =
             let uu____2084 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____2084 in
           if uu____2083
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____2090 = new_uvar "intro" env' typ' in
              bind uu____2090
                (fun u  ->
                   let uu____2097 =
                     let uu____2098 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____2098 in
                   if uu____2097
                   then
                     let uu____2101 =
                       let uu____2104 =
                         let uu___303_2105 = goal in
                         let uu____2106 = bnorm env' u in
                         let uu____2107 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2106;
                           FStar_Tactics_Types.goal_ty = uu____2107;
                           FStar_Tactics_Types.opts =
                             (uu___303_2105.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___303_2105.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____2104 in
                     bind uu____2101 (fun uu____2109  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2115 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____2115)
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
       (let uu____2136 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____2136 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2155 =
              let uu____2156 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____2156 in
            if uu____2155
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____2172 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____2172; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____2174 =
                 let uu____2177 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____2177 in
               bind uu____2174
                 (fun u  ->
                    let lb =
                      let uu____2193 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2193 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2197 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2197 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2234 =
                            let uu____2237 =
                              let uu___304_2238 = goal in
                              let uu____2239 = bnorm env' u in
                              let uu____2240 =
                                let uu____2241 = comp_to_typ c in
                                bnorm env' uu____2241 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2239;
                                FStar_Tactics_Types.goal_ty = uu____2240;
                                FStar_Tactics_Types.opts =
                                  (uu___304_2238.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___304_2238.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2237 in
                          bind uu____2234
                            (fun uu____2248  ->
                               let uu____2249 =
                                 let uu____2254 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2254, b) in
                               ret uu____2249)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2268 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2268))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2292 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2292 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___305_2299 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___305_2299.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___305_2299.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___305_2299.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2317 =
          bind get
            (fun ps  ->
               let uu____2323 = __tc e t in
               bind uu____2323
                 (fun uu____2345  ->
                    match uu____2345 with
                    | (t1,uu____2355,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2361 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2361 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2317
let refine_intro: Prims.unit tac =
  let uu____2371 =
    bind cur_goal
      (fun g  ->
         let uu____2378 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
         match uu____2378 with
         | (uu____2391,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___306_2416 = g in
               {
                 FStar_Tactics_Types.context =
                   (uu___306_2416.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___306_2416.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___306_2416.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___306_2416.FStar_Tactics_Types.is_guard)
               } in
             let uu____2417 =
               let uu____2422 =
                 let uu____2427 =
                   let uu____2428 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2428] in
                 FStar_Syntax_Subst.open_term uu____2427 phi in
               match uu____2422 with
               | (bvs,phi1) ->
                   let uu____2435 =
                     let uu____2436 = FStar_List.hd bvs in
                     FStar_Pervasives_Native.fst uu____2436 in
                   (uu____2435, phi1) in
             (match uu____2417 with
              | (bv1,phi1) ->
                  let uu____2449 =
                    let uu____2452 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1 in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2452
                      g.FStar_Tactics_Types.opts in
                  bind uu____2449
                    (fun g2  ->
                       bind dismiss (fun uu____2456  -> add_goals [g1; g2])))) in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2371
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
             let uu____2480 = __tc env t in
             bind uu____2480
               (fun uu____2500  ->
                  match uu____2500 with
                  | (t1,typ,guard) ->
                      let uu____2512 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts in
                      bind uu____2512
                        (fun uu____2519  ->
                           mlog
                             (fun uu____2523  ->
                                let uu____2524 =
                                  tts goal.FStar_Tactics_Types.context typ in
                                let uu____2525 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2524
                                  uu____2525)
                             (fun uu____2528  ->
                                let uu____2529 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty in
                                if uu____2529
                                then solve goal t1
                                else
                                  (let uu____2533 =
                                     tts goal.FStar_Tactics_Types.context t1 in
                                   let uu____2534 =
                                     tts goal.FStar_Tactics_Types.context typ in
                                   let uu____2535 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty in
                                   fail3
                                     "%s : %s does not exactly solve the goal %s"
                                     uu____2533 uu____2534 uu____2535)))))
let t_exact:
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2549 =
          mlog
            (fun uu____2554  ->
               let uu____2555 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "exact: tm = %s\n" uu____2555)
            (fun uu____2558  ->
               let uu____2559 =
                 let uu____2566 =
                   __exact_now set_expected_typ1 force_guard tm in
                 trytac' uu____2566 in
               bind uu____2559
                 (fun uu___280_2575  ->
                    match uu___280_2575 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2584 =
                          let uu____2591 =
                            let uu____2594 =
                              norm [FStar_Syntax_Embeddings.Delta] in
                            bind uu____2594
                              (fun uu____2598  ->
                                 bind refine_intro
                                   (fun uu____2600  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm)) in
                          trytac' uu____2591 in
                        bind uu____2584
                          (fun uu___279_2607  ->
                             match uu___279_2607 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2615 -> fail e))) in
        FStar_All.pipe_left (wrap_err "exact") uu____2549
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2630 =
             let uu____2637 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2637 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2630 in
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
          let uu____2697 = f x in
          bind uu____2697
            (fun y  ->
               let uu____2705 = mapM f xs in
               bind uu____2705 (fun ys  -> ret (y :: ys)))
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2723 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2740 =
               let uu____2745 = t_exact false true tm in trytac uu____2745 in
             bind uu____2740
               (fun uu___281_2752  ->
                  match uu___281_2752 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2758 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2758 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2790  ->
                                let uu____2791 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2791)
                             (fun uu____2794  ->
                                let uu____2795 =
                                  let uu____2796 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2796 in
                                if uu____2795
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2800 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2800
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2820 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2820 in
                                        let uu____2821 =
                                          __apply uopt tm' typ' in
                                        bind uu____2821
                                          (fun uu____2829  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2831 =
                                               let uu____2832 =
                                                 let uu____2835 =
                                                   let uu____2836 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2836 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2835 in
                                               uu____2832.FStar_Syntax_Syntax.n in
                                             match uu____2831 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2864) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2892 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2892
                                                      then ret ()
                                                      else
                                                        (let uu____2896 =
                                                           let uu____2899 =
                                                             let uu___307_2900
                                                               = goal in
                                                             let uu____2901 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2902 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___307_2900.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2901;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2902;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___307_2900.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2899] in
                                                         add_goals uu____2896))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2948 =
        mlog
          (fun uu____2953  ->
             let uu____2954 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2954)
          (fun uu____2956  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2960 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2960
                    (fun uu____2981  ->
                       match uu____2981 with
                       | (tm1,typ,guard) ->
                           let uu____2993 =
                             let uu____2996 =
                               let uu____2999 = __apply uopt tm1 typ in
                               bind uu____2999
                                 (fun uu____3003  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2996 in
                           let uu____3004 =
                             let uu____3007 =
                               tts goal.FStar_Tactics_Types.context tm1 in
                             let uu____3008 =
                               tts goal.FStar_Tactics_Types.context typ in
                             let uu____3009 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3007 uu____3008 uu____3009 in
                           try_unif uu____2993 uu____3004))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2948
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____3021 =
      let uu____3024 =
        mlog
          (fun uu____3029  ->
             let uu____3030 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3030)
          (fun uu____3033  ->
             let is_unit_t t =
               let uu____3038 =
                 let uu____3039 = FStar_Syntax_Subst.compress t in
                 uu____3039.FStar_Syntax_Syntax.n in
               match uu____3038 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3043 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____3047 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____3047
                    (fun uu____3069  ->
                       match uu____3069 with
                       | (tm1,t,guard) ->
                           let uu____3081 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____3081 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3111 =
                                     FStar_List.fold_left
                                       (fun uu____3157  ->
                                          fun uu____3158  ->
                                            match (uu____3157, uu____3158)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____3261 =
                                                  is_unit_t b_t in
                                                if uu____3261
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3299 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____3299 with
                                                   | (u,uu____3329,g_u) ->
                                                       let uu____3343 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____3343,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____3111 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3413 =
                                         let uu____3422 =
                                           let uu____3431 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3431.FStar_Syntax_Syntax.effect_args in
                                         match uu____3422 with
                                         | pre::post::uu____3442 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3483 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3413 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3515 =
                                                let uu____3524 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3524] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3515 in
                                            let uu____3525 =
                                              let uu____3526 =
                                                let uu____3527 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3527
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3526 in
                                            if uu____3525
                                            then
                                              let uu____3530 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3531 =
                                                let uu____3532 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1 in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3532 in
                                              let uu____3533 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3530 uu____3531
                                                uu____3533
                                            else
                                              (let solution =
                                                 let uu____3536 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3536 in
                                               let uu____3537 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3537
                                                 (fun uu____3542  ->
                                                    let uu____3543 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit in
                                                    bind uu____3543
                                                      (fun uu____3551  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3562 =
                                                               let uu____3569
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3569 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3562 in
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
                                                           let uu____3610 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3610
                                                           with
                                                           | (hd1,uu____3626)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3648)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3673
                                                                    -> false) in
                                                         let uu____3674 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3746
                                                                    ->
                                                                   match uu____3746
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3774)
                                                                    ->
                                                                    let uu____3775
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____3775
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3801)
                                                                    ->
                                                                    let uu____3822
                                                                    =
                                                                    let uu____3823
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3823.FStar_Syntax_Syntax.n in
                                                                    (match uu____3822
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3836
                                                                    ->
                                                                    let uu____3853
                                                                    =
                                                                    let uu____3862
                                                                    =
                                                                    let uu____3865
                                                                    =
                                                                    let uu___310_3866
                                                                    = goal in
                                                                    let uu____3867
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3868
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___310_3866.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3867;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3868;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___310_3866.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___310_3866.FStar_Tactics_Types.is_guard)
                                                                    } in
                                                                    [uu____3865] in
                                                                    (uu____3862,
                                                                    []) in
                                                                    ret
                                                                    uu____3853
                                                                    | 
                                                                    uu____3881
                                                                    ->
                                                                    let term1
                                                                    =
                                                                    bnorm env
                                                                    term in
                                                                    let uu____3883
                                                                    =
                                                                    let uu____3890
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3890
                                                                    term1 in
                                                                    (match uu____3883
                                                                    with
                                                                    | 
                                                                    (uu____3901,uu____3902,g_typ)
                                                                    ->
                                                                    let uu____3904
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts in
                                                                    bind
                                                                    uu____3904
                                                                    (fun
                                                                    uu___282_3920
                                                                     ->
                                                                    match uu___282_3920
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
                                                         bind uu____3674
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3988
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3988 in
                                                              let smt_goals =
                                                                let uu____4010
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____4010 in
                                                              let rec filter'
                                                                f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4066
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____4066
                                                                    then
                                                                    let uu____4069
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____4069
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                              let sub_goals1
                                                                =
                                                                filter'
                                                                  (fun g  ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4083
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____4083)
                                                                  sub_goals in
                                                              let uu____4084
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts in
                                                              bind uu____4084
                                                                (fun
                                                                   uu____4089
                                                                    ->
                                                                   let uu____4090
                                                                    =
                                                                    let uu____4093
                                                                    =
                                                                    let uu____4094
                                                                    =
                                                                    let uu____4095
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4095 in
                                                                    Prims.op_Negation
                                                                    uu____4094 in
                                                                    if
                                                                    uu____4093
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret () in
                                                                   bind
                                                                    uu____4090
                                                                    (fun
                                                                    uu____4101
                                                                     ->
                                                                    let uu____4102
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals in
                                                                    bind
                                                                    uu____4102
                                                                    (fun
                                                                    uu____4106
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))) in
      focus uu____3024 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3021
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4126 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____4126 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4136::(e1,uu____4138)::(e2,uu____4140)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4199 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4221 = destruct_eq' typ in
    match uu____4221 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4251 = FStar_Syntax_Util.un_squash typ in
        (match uu____4251 with
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
        let uu____4307 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____4307 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4355 = aux e' in
               FStar_Util.map_opt uu____4355
                 (fun uu____4379  ->
                    match uu____4379 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____4400 = aux e in
      FStar_Util.map_opt uu____4400
        (fun uu____4424  ->
           match uu____4424 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____4479 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____4479
            (fun uu____4503  ->
               match uu____4503 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___311_4520 = bv in
                     let uu____4521 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___311_4520.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___311_4520.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4521
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___312_4530 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___312_4530.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___312_4530.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4543 = h in
         match uu____4543 with
         | (bv,uu____4547) ->
             mlog
               (fun uu____4551  ->
                  let uu____4552 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4553 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4552
                    uu____4553)
               (fun uu____4556  ->
                  let uu____4557 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4557 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4586 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4586 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4601 =
                             let uu____4602 = FStar_Syntax_Subst.compress x in
                             uu____4602.FStar_Syntax_Syntax.n in
                           (match uu____4601 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___313_4615 = bv1 in
                                  let uu____4616 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___313_4615.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___313_4615.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4616
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4622 =
                                  let uu___314_4623 = goal in
                                  let uu____4624 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4625 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4626 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4624;
                                    FStar_Tactics_Types.witness = uu____4625;
                                    FStar_Tactics_Types.goal_ty = uu____4626;
                                    FStar_Tactics_Types.opts =
                                      (uu___314_4623.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___314_4623.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4622
                            | uu____4627 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4628 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4653 = b in
           match uu____4653 with
           | (bv,uu____4657) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___315_4661 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___315_4661.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___315_4661.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4665 =
                   let uu____4666 =
                     let uu____4673 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4673) in
                   FStar_Syntax_Syntax.NT uu____4666 in
                 [uu____4665] in
               let uu____4674 = subst_goal bv bv' s1 goal in
               (match uu____4674 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4693 = b in
         match uu____4693 with
         | (bv,uu____4697) ->
             let uu____4698 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4698 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4727 = FStar_Syntax_Util.type_u () in
                  (match uu____4727 with
                   | (ty,u) ->
                       let uu____4736 = new_uvar "binder_retype" e0 ty in
                       bind uu____4736
                         (fun t'  ->
                            let bv'' =
                              let uu___316_4746 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___316_4746.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___316_4746.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4750 =
                                let uu____4751 =
                                  let uu____4758 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4758) in
                                FStar_Syntax_Syntax.NT uu____4751 in
                              [uu____4750] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___317_4766 = b1 in
                                   let uu____4767 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___317_4766.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___317_4766.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4767
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4773  ->
                                 let uu____4774 =
                                   let uu____4777 =
                                     let uu____4780 =
                                       let uu___318_4781 = goal in
                                       let uu____4782 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4783 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4782;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4783;
                                         FStar_Tactics_Types.opts =
                                           (uu___318_4781.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___318_4781.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4780] in
                                   add_goals uu____4777 in
                                 bind uu____4774
                                   (fun uu____4786  ->
                                      let uu____4787 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4787
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4808 = b in
           match uu____4808 with
           | (bv,uu____4812) ->
               let uu____4813 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4813 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4845 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4845 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___319_4850 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___319_4850.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___319_4850.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___320_4854 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___320_4854.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___320_4854.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___320_4854.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___320_4854.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4860 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4860 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4882 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4882 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___321_4916 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___321_4916.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___321_4916.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4927 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4927 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4948 = FStar_Syntax_Print.bv_to_string x in
               let uu____4949 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4948 uu____4949
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4956 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4956 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4978 = FStar_Util.set_mem x fns_ty in
           if uu____4978
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4982 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4982
                (fun u  ->
                   let uu____4988 =
                     let uu____4989 = trysolve goal u in
                     Prims.op_Negation uu____4989 in
                   if uu____4988
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___322_4994 = goal in
                        let uu____4995 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4995;
                          FStar_Tactics_Types.goal_ty =
                            (uu___322_4994.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___322_4994.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___322_4994.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4997  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____5008 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____5008 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____5032  ->
                    let uu____5033 = clear b in
                    bind uu____5033
                      (fun uu____5037  ->
                         bind intro (fun uu____5039  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___323_5055 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___323_5055.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___323_5055.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___323_5055.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___323_5055.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5057  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___324_5073 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___324_5073.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___324_5073.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___324_5073.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___324_5073.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5075  -> add_goals [g']))
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
            let uu____5107 = FStar_Syntax_Subst.compress t in
            uu____5107.FStar_Syntax_Syntax.n in
          let uu____5110 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___326_5116 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___326_5116.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___326_5116.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____5110
            (fun t1  ->
               let tn1 =
                 let uu____5124 =
                   let uu____5125 = FStar_Syntax_Subst.compress t1 in
                   uu____5125.FStar_Syntax_Syntax.n in
                 match uu____5124 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____5157 = ff hd1 in
                     bind uu____5157
                       (fun hd2  ->
                          let fa uu____5177 =
                            match uu____5177 with
                            | (a,q) ->
                                let uu____5190 = ff a in
                                bind uu____5190 (fun a1  -> ret (a1, q)) in
                          let uu____5203 = mapM fa args in
                          bind uu____5203
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5263 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____5263 with
                      | (bs1,t') ->
                          let uu____5272 =
                            let uu____5275 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____5275 t' in
                          bind uu____5272
                            (fun t''  ->
                               let uu____5279 =
                                 let uu____5280 =
                                   let uu____5297 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____5298 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____5297, uu____5298, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____5280 in
                               ret uu____5279))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5319 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___325_5326 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___325_5326.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___325_5326.FStar_Syntax_Syntax.vars)
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
            let uu____5355 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____5355 with
            | (t1,lcomp,g) ->
                let uu____5367 =
                  (let uu____5370 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____5370) ||
                    (let uu____5372 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____5372) in
                if uu____5367
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____5382 = new_uvar "pointwise_rec" env typ in
                     bind uu____5382
                       (fun ut  ->
                          log ps
                            (fun uu____5393  ->
                               let uu____5394 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____5395 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5394 uu____5395);
                          (let uu____5396 =
                             let uu____5399 =
                               let uu____5400 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____5400 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5399 opts in
                           bind uu____5396
                             (fun uu____5403  ->
                                let uu____5404 =
                                  bind tau
                                    (fun uu____5410  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____5416  ->
                                            let uu____5417 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____5418 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5417 uu____5418);
                                       ret ut1) in
                                focus uu____5404))) in
                   let uu____5419 = trytac' rewrite_eq in
                   bind uu____5419
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
           let uu____5461 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5461 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5498  ->
                     let uu____5499 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5499);
                bind dismiss_all
                  (fun uu____5502  ->
                     let uu____5503 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5503
                       (fun gt'  ->
                          log ps
                            (fun uu____5513  ->
                               let uu____5514 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5514);
                          (let uu____5515 = push_goals gs in
                           bind uu____5515
                             (fun uu____5519  ->
                                add_goals
                                  [(let uu___327_5521 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___327_5521.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___327_5521.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___327_5521.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___327_5521.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5541 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5541 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5553 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5553 with
            | (hd1,args) ->
                let uu____5586 =
                  let uu____5599 =
                    let uu____5600 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5600.FStar_Syntax_Syntax.n in
                  (uu____5599, args) in
                (match uu____5586 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5614::(l,uu____5616)::(r,uu____5618)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5665 =
                       let uu____5666 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5666 in
                     if uu____5665
                     then
                       let uu____5669 = tts g.FStar_Tactics_Types.context l in
                       let uu____5670 = tts g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5669 uu____5670
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5673) ->
                     let uu____5690 = tts g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5690))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5698 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5698
         (fun u  ->
            let g' =
              let uu___328_5705 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___328_5705.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___328_5705.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___328_5705.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___328_5705.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5708  ->
                 let uu____5709 =
                   let uu____5712 =
                     let uu____5713 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5713
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5712
                     g.FStar_Tactics_Types.opts in
                 bind uu____5709
                   (fun uu____5716  ->
                      let uu____5717 = add_goals [g'] in
                      bind uu____5717 (fun uu____5721  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___329_5738 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___329_5738.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___329_5738.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___329_5738.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___329_5738.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___329_5738.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___329_5738.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___329_5738.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___329_5738.FStar_Tactics_Types.entry_range)
              })
       | uu____5739 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___330_5754 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___330_5754.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___330_5754.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___330_5754.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___330_5754.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___330_5754.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___330_5754.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___330_5754.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___330_5754.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5761 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5779 =
      bind cur_goal
        (fun g  ->
           let uu____5793 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5793
             (fun uu____5829  ->
                match uu____5829 with
                | (t1,typ,guard) ->
                    let uu____5845 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5845 with
                     | (hd1,args) ->
                         let uu____5888 =
                           let uu____5901 =
                             let uu____5902 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5902.FStar_Syntax_Syntax.n in
                           (uu____5901, args) in
                         (match uu____5888 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5921)::(q,uu____5923)::[]) when
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
                                let uu___331_5961 = g in
                                let uu____5962 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5962;
                                  FStar_Tactics_Types.witness =
                                    (uu___331_5961.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___331_5961.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___331_5961.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___331_5961.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___332_5964 = g in
                                let uu____5965 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5965;
                                  FStar_Tactics_Types.witness =
                                    (uu___332_5964.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___332_5964.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___332_5964.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___332_5964.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5972  ->
                                   let uu____5973 = add_goals [g1; g2] in
                                   bind uu____5973
                                     (fun uu____5982  ->
                                        let uu____5983 =
                                          let uu____5988 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5989 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5988, uu____5989) in
                                        ret uu____5983))
                          | uu____5994 ->
                              let uu____6007 =
                                tts g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____6007)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5779
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6045 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____6045);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___333_6052 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___333_6052.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___333_6052.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___333_6052.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___333_6052.FStar_Tactics_Types.is_guard)
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
      let uu____6088 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____6096 = __tc env tm in
             bind uu____6096
               (fun uu____6116  ->
                  match uu____6116 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____6088
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____6147 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6153 =
              let uu____6154 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6154 in
            new_uvar "uvar_env.2" env uu____6153 in
      bind uu____6147
        (fun typ  ->
           let uu____6166 = new_uvar "uvar_env" env typ in
           bind uu____6166 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____6178 =
      bind cur_goal
        (fun goal  ->
           let uu____6184 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____6184
             (fun uu____6204  ->
                match uu____6204 with
                | (t1,typ,guard) ->
                    let uu____6216 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____6216
                      (fun uu____6221  ->
                         let uu____6222 =
                           let uu____6225 =
                             let uu___334_6226 = goal in
                             let uu____6227 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____6228 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___334_6226.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6227;
                               FStar_Tactics_Types.goal_ty = uu____6228;
                               FStar_Tactics_Types.opts =
                                 (uu___334_6226.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____6225] in
                         add_goals uu____6222))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6178
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6246 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____6246)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6263  ->
             let uu____6264 = FStar_Options.unsafe_tactic_exec () in
             if uu____6264
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6270  -> fun uu____6271  -> false) in
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
      let uu____6291 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____6291 with
      | (u,uu____6309,g_u) ->
          let g =
            let uu____6324 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6324;
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
      let uu____6339 = goal_of_goal_ty env typ in
      match uu____6339 with
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