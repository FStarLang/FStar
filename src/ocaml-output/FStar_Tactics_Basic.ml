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
      let uu____529 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____529 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____556 =
              let uu____559 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____559 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____556);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'Auu____617 . Prims.string -> 'Auu____617 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____628 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____628
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____633 . Prims.string -> Prims.string -> 'Auu____633 tac =
  fun msg  ->
    fun x  -> let uu____644 = FStar_Util.format1 msg x in fail uu____644
let fail2:
  'Auu____649 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____649 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____664 = FStar_Util.format2 msg x y in fail uu____664
let fail3:
  'Auu____670 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____670 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____689 = FStar_Util.format3 msg x y z in fail uu____689
let trytac': 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____719 = run t ps in
         match uu____719 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____740) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____765 = trytac' t in
    bind uu____765
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____792 -> ret FStar_Pervasives_Native.None)
let wrap_err: 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____818 = run t ps in
           match uu____818 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____835  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____848 =
          let uu____849 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck" in
          () in
        let debug_off uu____853 =
          let uu____854 = FStar_Options.set_options FStar_Options.Reset "" in
          () in
        (let uu____856 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346") in
         if uu____856
         then
           (debug_on ();
            (let uu____858 = FStar_Syntax_Print.term_to_string t1 in
             let uu____859 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____858
               uu____859))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2 in
           debug_off (); res
         with | uu____871 -> (debug_off (); false))
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____884 =
         let uu___62_885 = p in
         let uu____886 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___62_885.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___62_885.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___62_885.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____886;
           FStar_Tactics_Types.smt_goals =
             (uu___62_885.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___62_885.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___62_885.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___62_885.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___62_885.FStar_Tactics_Types.entry_range)
         } in
       set uu____884)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____899 = trysolve goal solution in
      if uu____899
      then dismiss
      else
        (let uu____903 =
           let uu____904 = tts goal.FStar_Tactics_Types.context solution in
           let uu____905 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____906 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____904 uu____905
             uu____906 in
         fail uu____903)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___63_913 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___63_913.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___63_913.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___63_913.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___63_913.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___63_913.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___63_913.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___63_913.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___63_913.FStar_Tactics_Types.entry_range)
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
      let uu____941 = FStar_TypeChecker_Env.pop_bv e in
      match uu____941 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____959 =
      (let uu____962 = aux b2 env in Prims.op_Negation uu____962) &&
        (let uu____964 = FStar_ST.op_Bang nwarn in
         uu____964 < (Prims.parse_int "5")) in
    if uu____959
    then
      ((let uu____985 =
          let uu____990 =
            let uu____991 = goal_to_string g in
            FStar_Util.format1
              "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
              uu____991 in
          (FStar_Errors.Warning_IllFormedGoal, uu____990) in
        FStar_Errors.log_issue
          (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____985);
       (let uu____992 =
          let uu____993 = FStar_ST.op_Bang nwarn in
          uu____993 + (Prims.parse_int "1") in
        FStar_ST.op_Colon_Equals nwarn uu____992))
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___64_1050 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___64_1050.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___64_1050.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___64_1050.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___64_1050.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___64_1050.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___64_1050.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___64_1050.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___64_1050.FStar_Tactics_Types.entry_range)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1068 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1068.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1068.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1068.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___65_1068.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1068.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1068.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1068.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1068.FStar_Tactics_Types.entry_range)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1086 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1086.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1086.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1086.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___66_1086.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___66_1086.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1086.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1086.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1086.FStar_Tactics_Types.entry_range)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___67_1104 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1104.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1104.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___67_1104.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___67_1104.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___67_1104.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1104.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1104.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1104.FStar_Tactics_Types.entry_range)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1113  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___68_1125 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___68_1125.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___68_1125.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___68_1125.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___68_1125.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___68_1125.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___68_1125.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___68_1125.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___68_1125.FStar_Tactics_Types.entry_range)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1151 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1151 with
        | (u,uu____1167,g_u) ->
            let uu____1181 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1181 (fun uu____1185  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1189 = FStar_Syntax_Util.un_squash t in
    match uu____1189 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1199 =
          let uu____1200 = FStar_Syntax_Subst.compress t' in
          uu____1200.FStar_Syntax_Syntax.n in
        (match uu____1199 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1204 -> false)
    | uu____1205 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1213 = FStar_Syntax_Util.un_squash t in
    match uu____1213 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1223 =
          let uu____1224 = FStar_Syntax_Subst.compress t' in
          uu____1224.FStar_Syntax_Syntax.n in
        (match uu____1223 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1228 -> false)
    | uu____1229 -> false
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
            let uu____1267 = env.FStar_TypeChecker_Env.universe_of env phi in
            FStar_Syntax_Util.mk_squash uu____1267 phi in
          let uu____1268 = new_uvar reason env typ in
          bind uu____1268
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
             let uu____1324 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1324
           with | e1 -> fail "not typeable")
let must_trivial: env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1372 =
          let uu____1373 =
            let uu____1374 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1374 in
          Prims.op_Negation uu____1373 in
        if uu____1372 then fail "got non-trivial guard" else ret ()
      with | uu____1383 -> fail "got non-trivial guard"
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1391 =
      bind cur_goal
        (fun goal  ->
           let uu____1397 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1397
             (fun uu____1417  ->
                match uu____1417 with
                | (t1,typ,guard) ->
                    let uu____1429 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____1429 (fun uu____1433  -> ret typ))) in
    FStar_All.pipe_left (wrap_err "tc") uu____1391
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1454 = mk_irrelevant_goal reason env phi opts in
          bind uu____1454 (fun goal  -> add_goals [goal])
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
       let uu____1474 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1474
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1478 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1478))
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
          let uu____1495 =
            let uu____1496 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1496.FStar_TypeChecker_Env.guard_f in
          match uu____1495 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1500 = istrivial e f in
              if uu____1500
              then ret ()
              else
                (let uu____1504 = mk_irrelevant_goal reason e f opts in
                 bind uu____1504
                   (fun goal  ->
                      let goal1 =
                        let uu___73_1511 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___73_1511.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___73_1511.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___73_1511.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___73_1511.FStar_Tactics_Types.opts);
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
          let uu____1532 =
            let uu____1533 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1533.FStar_TypeChecker_Env.guard_f in
          match uu____1532 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1541 = istrivial e f in
              if uu____1541
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1549 = mk_irrelevant_goal reason e f opts in
                 bind uu____1549
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___74_1559 = goal in
                            {
                              FStar_Tactics_Types.context =
                                (uu___74_1559.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___74_1559.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___74_1559.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___74_1559.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1565 = is_irrelevant g in
       if uu____1565
       then bind dismiss (fun uu____1569  -> add_smt_goals [g])
       else
         (let uu____1571 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1571))
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
             let uu____1612 =
               try
                 let uu____1646 =
                   let uu____1655 = FStar_BigInt.to_int_fs n1 in
                   FStar_List.splitAt uu____1655 p.FStar_Tactics_Types.goals in
                 ret uu____1646
               with | uu____1677 -> fail "divide: not enough goals" in
             bind uu____1612
               (fun uu____1704  ->
                  match uu____1704 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___75_1730 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___75_1730.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___75_1730.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___75_1730.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___75_1730.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___75_1730.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___75_1730.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___75_1730.FStar_Tactics_Types.entry_range)
                        } in
                      let rp =
                        let uu___76_1732 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___76_1732.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___76_1732.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___76_1732.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___76_1732.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___76_1732.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___76_1732.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___76_1732.FStar_Tactics_Types.entry_range)
                        } in
                      let uu____1733 = set lp in
                      bind uu____1733
                        (fun uu____1741  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1755 = set rp in
                                     bind uu____1755
                                       (fun uu____1763  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___77_1779 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___77_1779.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___77_1779.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___77_1779.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___77_1779.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___77_1779.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___77_1779.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___77_1779.FStar_Tactics_Types.entry_range)
                                                      } in
                                                    let uu____1780 = set p' in
                                                    bind uu____1780
                                                      (fun uu____1788  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1806 = divide FStar_BigInt.one f idtac in
    bind uu____1806
      (fun uu____1819  -> match uu____1819 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1853::uu____1854 ->
             let uu____1857 =
               let uu____1866 = map tau in
               divide FStar_BigInt.one tau uu____1866 in
             bind uu____1857
               (fun uu____1884  ->
                  match uu____1884 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1921 =
        bind t1
          (fun uu____1926  ->
             let uu____1927 = map t2 in
             bind uu____1927 (fun uu____1935  -> ret ())) in
      focus uu____1921
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1946 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1946 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1961 =
             let uu____1962 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1962 in
           if uu____1961
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1968 = new_uvar "intro" env' typ' in
              bind uu____1968
                (fun u  ->
                   let uu____1975 =
                     let uu____1976 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1976 in
                   if uu____1975
                   then
                     let uu____1979 =
                       let uu____1982 =
                         let uu___80_1983 = goal in
                         let uu____1984 = bnorm env' u in
                         let uu____1985 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1984;
                           FStar_Tactics_Types.goal_ty = uu____1985;
                           FStar_Tactics_Types.opts =
                             (uu___80_1983.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___80_1983.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1982 in
                     bind uu____1979 (fun uu____1987  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1993 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1993)
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
       (let uu____2014 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____2014 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2033 =
              let uu____2034 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____2034 in
            if uu____2033
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____2050 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____2050; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____2052 =
                 let uu____2055 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____2055 in
               bind uu____2052
                 (fun u  ->
                    let lb =
                      let uu____2071 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2071 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2075 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2075 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2112 =
                            let uu____2115 =
                              let uu___81_2116 = goal in
                              let uu____2117 = bnorm env' u in
                              let uu____2118 =
                                let uu____2119 = comp_to_typ c in
                                bnorm env' uu____2119 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2117;
                                FStar_Tactics_Types.goal_ty = uu____2118;
                                FStar_Tactics_Types.opts =
                                  (uu___81_2116.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___81_2116.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2115 in
                          bind uu____2112
                            (fun uu____2126  ->
                               let uu____2127 =
                                 let uu____2132 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2132, b) in
                               ret uu____2127)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2146 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2146))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2170 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2170 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___82_2177 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___82_2177.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___82_2177.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___82_2177.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2195 =
          bind get
            (fun ps  ->
               let uu____2201 = __tc e t in
               bind uu____2201
                 (fun uu____2223  ->
                    match uu____2223 with
                    | (t1,uu____2233,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2239 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2239 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2195
let refine_intro: Prims.unit tac =
  let uu____2249 =
    bind cur_goal
      (fun g  ->
         let uu____2256 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
         match uu____2256 with
         | (uu____2269,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___83_2294 = g in
               {
                 FStar_Tactics_Types.context =
                   (uu___83_2294.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___83_2294.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___83_2294.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___83_2294.FStar_Tactics_Types.is_guard)
               } in
             let uu____2295 =
               let uu____2300 =
                 let uu____2305 =
                   let uu____2306 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2306] in
                 FStar_Syntax_Subst.open_term uu____2305 phi in
               match uu____2300 with
               | (bvs,phi1) ->
                   let uu____2313 =
                     let uu____2314 = FStar_List.hd bvs in
                     FStar_Pervasives_Native.fst uu____2314 in
                   (uu____2313, phi1) in
             (match uu____2295 with
              | (bv1,phi1) ->
                  let uu____2327 =
                    let uu____2330 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1 in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2330
                      g.FStar_Tactics_Types.opts in
                  bind uu____2327
                    (fun g2  ->
                       bind dismiss (fun uu____2334  -> add_goals [g1; g2])))) in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2249
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
             let uu____2358 = __tc env t in
             bind uu____2358
               (fun uu____2378  ->
                  match uu____2378 with
                  | (t1,typ,guard) ->
                      let uu____2390 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts in
                      bind uu____2390
                        (fun uu____2397  ->
                           mlog
                             (fun uu____2401  ->
                                let uu____2402 =
                                  tts goal.FStar_Tactics_Types.context typ in
                                let uu____2403 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2402
                                  uu____2403)
                             (fun uu____2406  ->
                                let uu____2407 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty in
                                if uu____2407
                                then solve goal t1
                                else
                                  (let uu____2411 =
                                     tts goal.FStar_Tactics_Types.context t1 in
                                   let uu____2412 =
                                     tts goal.FStar_Tactics_Types.context typ in
                                   let uu____2413 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty in
                                   fail3
                                     "%s : %s does not exactly solve the goal %s"
                                     uu____2411 uu____2412 uu____2413)))))
let t_exact:
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2427 =
          mlog
            (fun uu____2432  ->
               let uu____2433 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "exact: tm = %s\n" uu____2433)
            (fun uu____2436  ->
               let uu____2437 =
                 let uu____2444 =
                   __exact_now set_expected_typ1 force_guard tm in
                 trytac' uu____2444 in
               bind uu____2437
                 (fun uu___57_2453  ->
                    match uu___57_2453 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2462 =
                          let uu____2469 =
                            let uu____2472 =
                              norm [FStar_Syntax_Embeddings.Delta] in
                            bind uu____2472
                              (fun uu____2476  ->
                                 bind refine_intro
                                   (fun uu____2478  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm)) in
                          trytac' uu____2469 in
                        bind uu____2462
                          (fun uu___56_2485  ->
                             match uu___56_2485 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2493 -> fail e))) in
        FStar_All.pipe_left (wrap_err "exact") uu____2427
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2508 =
             let uu____2515 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2515 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2508 in
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
          let uu____2575 = f x in
          bind uu____2575
            (fun y  ->
               let uu____2583 = mapM f xs in
               bind uu____2583 (fun ys  -> ret (y :: ys)))
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2601 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2618 =
               let uu____2623 = t_exact false true tm in trytac uu____2623 in
             bind uu____2618
               (fun uu___58_2630  ->
                  match uu___58_2630 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2636 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2636 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2668  ->
                                let uu____2669 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2669)
                             (fun uu____2672  ->
                                let uu____2673 =
                                  let uu____2674 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2674 in
                                if uu____2673
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2678 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2678
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2698 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2698 in
                                        let uu____2699 =
                                          __apply uopt tm' typ' in
                                        bind uu____2699
                                          (fun uu____2707  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2709 =
                                               let uu____2710 =
                                                 let uu____2713 =
                                                   let uu____2714 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2714 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2713 in
                                               uu____2710.FStar_Syntax_Syntax.n in
                                             match uu____2709 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2742) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2770 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2770
                                                      then ret ()
                                                      else
                                                        (let uu____2774 =
                                                           let uu____2777 =
                                                             let uu___84_2778
                                                               = goal in
                                                             let uu____2779 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2780 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___84_2778.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2779;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2780;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___84_2778.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2777] in
                                                         add_goals uu____2774))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2826 =
        mlog
          (fun uu____2831  ->
             let uu____2832 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2832)
          (fun uu____2834  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2838 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2838
                    (fun uu____2859  ->
                       match uu____2859 with
                       | (tm1,typ,guard) ->
                           let uu____2871 =
                             let uu____2874 =
                               let uu____2877 = __apply uopt tm1 typ in
                               bind uu____2877
                                 (fun uu____2881  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2874 in
                           let uu____2882 =
                             let uu____2885 =
                               tts goal.FStar_Tactics_Types.context tm1 in
                             let uu____2886 =
                               tts goal.FStar_Tactics_Types.context typ in
                             let uu____2887 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2885 uu____2886 uu____2887 in
                           try_unif uu____2871 uu____2882))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2826
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2899 =
      let uu____2902 =
        mlog
          (fun uu____2907  ->
             let uu____2908 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2908)
          (fun uu____2911  ->
             let is_unit_t t =
               let uu____2916 =
                 let uu____2917 = FStar_Syntax_Subst.compress t in
                 uu____2917.FStar_Syntax_Syntax.n in
               match uu____2916 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____2921 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____2925 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2925
                    (fun uu____2947  ->
                       match uu____2947 with
                       | (tm1,t,guard) ->
                           let uu____2959 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____2959 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____2989 =
                                     FStar_List.fold_left
                                       (fun uu____3035  ->
                                          fun uu____3036  ->
                                            match (uu____3035, uu____3036)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____3139 =
                                                  is_unit_t b_t in
                                                if uu____3139
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3177 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____3177 with
                                                   | (u,uu____3207,g_u) ->
                                                       let uu____3221 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____3221,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____2989 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3291 =
                                         let uu____3300 =
                                           let uu____3309 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3309.FStar_Syntax_Syntax.effect_args in
                                         match uu____3300 with
                                         | pre::post::uu____3320 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3361 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3291 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3393 =
                                                let uu____3402 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3402] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3393 in
                                            let uu____3403 =
                                              let uu____3404 =
                                                let uu____3405 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3405
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3404 in
                                            if uu____3403
                                            then
                                              let uu____3408 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3409 =
                                                let uu____3410 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1 in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3410 in
                                              let uu____3411 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3408 uu____3409
                                                uu____3411
                                            else
                                              (let uu____3413 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3413
                                                 (fun uu____3418  ->
                                                    let uu____3419 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit in
                                                    bind uu____3419
                                                      (fun uu____3427  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3438 =
                                                               let uu____3445
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3445 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3438 in
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
                                                           let uu____3486 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3486
                                                           with
                                                           | (hd1,uu____3502)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3524)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3549
                                                                    -> false) in
                                                         let uu____3550 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3622
                                                                    ->
                                                                   match uu____3622
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3650)
                                                                    ->
                                                                    let uu____3651
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____3651
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3677)
                                                                    ->
                                                                    let uu____3698
                                                                    =
                                                                    let uu____3699
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3699.FStar_Syntax_Syntax.n in
                                                                    (match uu____3698
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3712
                                                                    ->
                                                                    let uu____3729
                                                                    =
                                                                    let uu____3738
                                                                    =
                                                                    let uu____3741
                                                                    =
                                                                    let uu___87_3742
                                                                    = goal in
                                                                    let uu____3743
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3744
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___87_3742.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3743;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3744;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___87_3742.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___87_3742.FStar_Tactics_Types.is_guard)
                                                                    } in
                                                                    [uu____3741] in
                                                                    (uu____3738,
                                                                    []) in
                                                                    ret
                                                                    uu____3729
                                                                    | 
                                                                    uu____3757
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____3759
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    () in
                                                                    if
                                                                    uu____3759
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term in
                                                                    let uu____3762
                                                                    =
                                                                    let uu____3769
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3769
                                                                    term1 in
                                                                    match uu____3762
                                                                    with
                                                                    | 
                                                                    (uu____3770,uu____3771,g_typ)
                                                                    -> g_typ) in
                                                                    let uu____3773
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts in
                                                                    bind
                                                                    uu____3773
                                                                    (fun
                                                                    uu___59_3789
                                                                     ->
                                                                    match uu___59_3789
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
                                                                    ([], [g])))))) in
                                                         bind uu____3550
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3857
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3857 in
                                                              let smt_goals =
                                                                let uu____3879
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3879 in
                                                              let rec filter'
                                                                a f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____3934
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____3934
                                                                    then
                                                                    let uu____3937
                                                                    =
                                                                    filter'
                                                                    () f xs1 in
                                                                    x ::
                                                                    uu____3937
                                                                    else
                                                                    filter'
                                                                    () f xs1 in
                                                              let sub_goals1
                                                                =
                                                                Obj.magic
                                                                  (filter' ()
                                                                    (fun a434
                                                                     ->
                                                                    fun a435 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____3951
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____3951))
                                                                    a434 a435)
                                                                    (Obj.magic
                                                                    sub_goals)) in
                                                              let uu____3952
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts in
                                                              bind uu____3952
                                                                (fun
                                                                   uu____3957
                                                                    ->
                                                                   let uu____3958
                                                                    =
                                                                    let uu____3961
                                                                    =
                                                                    let uu____3962
                                                                    =
                                                                    let uu____3963
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____3963 in
                                                                    Prims.op_Negation
                                                                    uu____3962 in
                                                                    if
                                                                    uu____3961
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret () in
                                                                   bind
                                                                    uu____3958
                                                                    (fun
                                                                    uu____3969
                                                                     ->
                                                                    let uu____3970
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals in
                                                                    bind
                                                                    uu____3970
                                                                    (fun
                                                                    uu____3974
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))) in
      focus uu____2902 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2899
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3994 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3994 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4004::(e1,uu____4006)::(e2,uu____4008)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4067 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4089 = destruct_eq' typ in
    match uu____4089 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4119 = FStar_Syntax_Util.un_squash typ in
        (match uu____4119 with
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
        let uu____4175 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____4175 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4223 = aux e' in
               FStar_Util.map_opt uu____4223
                 (fun uu____4247  ->
                    match uu____4247 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____4268 = aux e in
      FStar_Util.map_opt uu____4268
        (fun uu____4292  ->
           match uu____4292 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____4347 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____4347
            (fun uu____4371  ->
               match uu____4371 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___88_4388 = bv in
                     let uu____4389 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___88_4388.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___88_4388.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4389
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___89_4398 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___89_4398.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___89_4398.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4411 = h in
         match uu____4411 with
         | (bv,uu____4415) ->
             mlog
               (fun uu____4419  ->
                  let uu____4420 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4421 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4420
                    uu____4421)
               (fun uu____4424  ->
                  let uu____4425 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4425 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4454 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4454 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4469 =
                             let uu____4470 = FStar_Syntax_Subst.compress x in
                             uu____4470.FStar_Syntax_Syntax.n in
                           (match uu____4469 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___90_4483 = bv1 in
                                  let uu____4484 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___90_4483.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___90_4483.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4484
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4490 =
                                  let uu___91_4491 = goal in
                                  let uu____4492 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4493 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4494 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4492;
                                    FStar_Tactics_Types.witness = uu____4493;
                                    FStar_Tactics_Types.goal_ty = uu____4494;
                                    FStar_Tactics_Types.opts =
                                      (uu___91_4491.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___91_4491.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4490
                            | uu____4495 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4496 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4521 = b in
           match uu____4521 with
           | (bv,uu____4525) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___92_4529 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___92_4529.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___92_4529.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4533 =
                   let uu____4534 =
                     let uu____4541 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4541) in
                   FStar_Syntax_Syntax.NT uu____4534 in
                 [uu____4533] in
               let uu____4542 = subst_goal bv bv' s1 goal in
               (match uu____4542 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4561 = b in
         match uu____4561 with
         | (bv,uu____4565) ->
             let uu____4566 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4566 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4595 = FStar_Syntax_Util.type_u () in
                  (match uu____4595 with
                   | (ty,u) ->
                       let uu____4604 = new_uvar "binder_retype" e0 ty in
                       bind uu____4604
                         (fun t'  ->
                            let bv'' =
                              let uu___93_4614 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___93_4614.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___93_4614.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4618 =
                                let uu____4619 =
                                  let uu____4626 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4626) in
                                FStar_Syntax_Syntax.NT uu____4619 in
                              [uu____4618] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___94_4634 = b1 in
                                   let uu____4635 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___94_4634.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___94_4634.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4635
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4641  ->
                                 let uu____4642 =
                                   let uu____4645 =
                                     let uu____4648 =
                                       let uu___95_4649 = goal in
                                       let uu____4650 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4651 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4650;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4651;
                                         FStar_Tactics_Types.opts =
                                           (uu___95_4649.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___95_4649.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4648] in
                                   add_goals uu____4645 in
                                 bind uu____4642
                                   (fun uu____4654  ->
                                      let uu____4655 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4655
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4676 = b in
           match uu____4676 with
           | (bv,uu____4680) ->
               let uu____4681 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4681 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4713 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4713 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___96_4718 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___96_4718.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___96_4718.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___97_4722 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___97_4722.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___97_4722.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___97_4722.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___97_4722.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4728 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4728 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4750 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4750 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___98_4784 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___98_4784.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___98_4784.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4795 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4795 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4816 = FStar_Syntax_Print.bv_to_string x in
               let uu____4817 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4816 uu____4817
             else revert)
let free_in: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool
  =
  fun bv  ->
    fun t  ->
      let uu____4825 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____4825
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____4841  ->
              let uu____4842 = FStar_Syntax_Print.binder_to_string b in
              let uu____4843 =
                let uu____4844 =
                  let uu____4845 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context in
                  FStar_All.pipe_right uu____4845 FStar_List.length in
                FStar_All.pipe_right uu____4844 FStar_Util.string_of_int in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____4842 uu____4843)
           (fun uu____4856  ->
              let uu____4857 = split_env bv goal.FStar_Tactics_Types.context in
              match uu____4857 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____4902 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort in
                        if uu____4902
                        then
                          let uu____4905 =
                            let uu____4906 =
                              FStar_Syntax_Print.bv_to_string bv' in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____4906 in
                          fail uu____4905
                        else check bvs2 in
                  let uu____4908 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty in
                  if uu____4908
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____4912 = check bvs in
                     bind uu____4912
                       (fun uu____4918  ->
                          let env' = push_bvs e' bvs in
                          let uu____4920 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty in
                          bind uu____4920
                            (fun ut  ->
                               let uu____4926 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut in
                               if uu____4926
                               then
                                 replace_cur
                                   (let uu___99_4931 = goal in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness = ut;
                                      FStar_Tactics_Types.goal_ty =
                                        (uu___99_4931.FStar_Tactics_Types.goal_ty);
                                      FStar_Tactics_Types.opts =
                                        (uu___99_4931.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___99_4931.FStar_Tactics_Types.is_guard)
                                    })
                               else
                                 fail
                                   "Cannot clear; binder appears in witness")))))
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4938 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4938 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____4952) ->
           let uu____4957 = FStar_Syntax_Syntax.mk_binder x in
           clear uu____4957)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___100_4973 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___100_4973.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___100_4973.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___100_4973.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___100_4973.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4975  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___101_4991 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___101_4991.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___101_4991.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___101_4991.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___101_4991.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4993  -> add_goals [g']))
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
            let uu____5025 = FStar_Syntax_Subst.compress t in
            uu____5025.FStar_Syntax_Syntax.n in
          let uu____5028 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___103_5034 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___103_5034.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___103_5034.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____5028
            (fun t1  ->
               let tn1 =
                 let uu____5042 =
                   let uu____5043 = FStar_Syntax_Subst.compress t1 in
                   uu____5043.FStar_Syntax_Syntax.n in
                 match uu____5042 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____5075 = ff hd1 in
                     bind uu____5075
                       (fun hd2  ->
                          let fa uu____5095 =
                            match uu____5095 with
                            | (a,q) ->
                                let uu____5108 = ff a in
                                bind uu____5108 (fun a1  -> ret (a1, q)) in
                          let uu____5121 = mapM fa args in
                          bind uu____5121
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5181 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____5181 with
                      | (bs1,t') ->
                          let uu____5190 =
                            let uu____5193 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____5193 t' in
                          bind uu____5190
                            (fun t''  ->
                               let uu____5197 =
                                 let uu____5198 =
                                   let uu____5215 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____5216 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____5215, uu____5216, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____5198 in
                               ret uu____5197))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5237 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___102_5244 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___102_5244.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___102_5244.FStar_Syntax_Syntax.vars)
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
            let uu____5273 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____5273 with
            | (t1,lcomp,g) ->
                let uu____5285 =
                  (let uu____5288 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____5288) ||
                    (let uu____5290 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____5290) in
                if uu____5285
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____5300 = new_uvar "pointwise_rec" env typ in
                     bind uu____5300
                       (fun ut  ->
                          log ps
                            (fun uu____5311  ->
                               let uu____5312 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____5313 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5312 uu____5313);
                          (let uu____5314 =
                             let uu____5317 =
                               let uu____5318 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____5318 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5317 opts in
                           bind uu____5314
                             (fun uu____5321  ->
                                let uu____5322 =
                                  bind tau
                                    (fun uu____5328  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____5334  ->
                                            let uu____5335 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____5336 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5335 uu____5336);
                                       ret ut1) in
                                focus uu____5322))) in
                   let uu____5337 = trytac' rewrite_eq in
                   bind uu____5337
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
           let uu____5379 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5379 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5416  ->
                     let uu____5417 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5417);
                bind dismiss_all
                  (fun uu____5420  ->
                     let uu____5421 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5421
                       (fun gt'  ->
                          log ps
                            (fun uu____5431  ->
                               let uu____5432 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5432);
                          (let uu____5433 = push_goals gs in
                           bind uu____5433
                             (fun uu____5437  ->
                                add_goals
                                  [(let uu___104_5439 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___104_5439.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___104_5439.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___104_5439.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___104_5439.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5459 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5459 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5471 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5471 with
            | (hd1,args) ->
                let uu____5504 =
                  let uu____5517 =
                    let uu____5518 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5518.FStar_Syntax_Syntax.n in
                  (uu____5517, args) in
                (match uu____5504 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5532::(l,uu____5534)::(r,uu____5536)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5583 =
                       let uu____5584 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5584 in
                     if uu____5583
                     then
                       let uu____5587 = tts g.FStar_Tactics_Types.context l in
                       let uu____5588 = tts g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5587 uu____5588
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5591) ->
                     let uu____5608 = tts g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5608))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5616 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5616
         (fun u  ->
            let g' =
              let uu___105_5623 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___105_5623.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___105_5623.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___105_5623.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___105_5623.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5626  ->
                 let uu____5627 =
                   let uu____5630 =
                     let uu____5631 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5631
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5630
                     g.FStar_Tactics_Types.opts in
                 bind uu____5627
                   (fun uu____5634  ->
                      let uu____5635 = add_goals [g'] in
                      bind uu____5635 (fun uu____5639  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___106_5656 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___106_5656.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___106_5656.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___106_5656.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___106_5656.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___106_5656.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___106_5656.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___106_5656.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___106_5656.FStar_Tactics_Types.entry_range)
              })
       | uu____5657 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___107_5672 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___107_5672.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___107_5672.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___107_5672.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___107_5672.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___107_5672.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___107_5672.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___107_5672.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___107_5672.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5679 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5697 =
      bind cur_goal
        (fun g  ->
           let uu____5711 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5711
             (fun uu____5747  ->
                match uu____5747 with
                | (t1,typ,guard) ->
                    let uu____5763 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5763 with
                     | (hd1,args) ->
                         let uu____5806 =
                           let uu____5819 =
                             let uu____5820 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5820.FStar_Syntax_Syntax.n in
                           (uu____5819, args) in
                         (match uu____5806 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5839)::(q,uu____5841)::[]) when
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
                                let uu___108_5879 = g in
                                let uu____5880 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5880;
                                  FStar_Tactics_Types.witness =
                                    (uu___108_5879.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___108_5879.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___108_5879.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___108_5879.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___109_5882 = g in
                                let uu____5883 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5883;
                                  FStar_Tactics_Types.witness =
                                    (uu___109_5882.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___109_5882.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___109_5882.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___109_5882.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5890  ->
                                   let uu____5891 = add_goals [g1; g2] in
                                   bind uu____5891
                                     (fun uu____5900  ->
                                        let uu____5901 =
                                          let uu____5906 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5907 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5906, uu____5907) in
                                        ret uu____5901))
                          | uu____5912 ->
                              let uu____5925 =
                                tts g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5925)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5697
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5963 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5963);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___110_5970 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___110_5970.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___110_5970.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___110_5970.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___110_5970.FStar_Tactics_Types.is_guard)
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
      let uu____6006 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____6014 = __tc env tm in
             bind uu____6014
               (fun uu____6034  ->
                  match uu____6034 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____6006
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____6065 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6071 =
              let uu____6072 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6072 in
            new_uvar "uvar_env.2" env uu____6071 in
      bind uu____6065
        (fun typ  ->
           let uu____6084 = new_uvar "uvar_env" env typ in
           bind uu____6084 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____6096 =
      bind cur_goal
        (fun goal  ->
           let uu____6102 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____6102
             (fun uu____6122  ->
                match uu____6122 with
                | (t1,typ,guard) ->
                    let uu____6134 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____6134
                      (fun uu____6139  ->
                         let uu____6140 =
                           let uu____6143 =
                             let uu___111_6144 = goal in
                             let uu____6145 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____6146 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___111_6144.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6145;
                               FStar_Tactics_Types.goal_ty = uu____6146;
                               FStar_Tactics_Types.opts =
                                 (uu___111_6144.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____6143] in
                         add_goals uu____6140))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6096
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6164 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____6164)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6181  ->
             let uu____6182 = FStar_Options.unsafe_tactic_exec () in
             if uu____6182
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6188  -> fun uu____6189  -> false) in
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
      let uu____6209 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____6209 with
      | (u,uu____6227,g_u) ->
          let g =
            let uu____6242 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6242;
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
      let uu____6257 = goal_of_goal_ty env typ in
      match uu____6257 with
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