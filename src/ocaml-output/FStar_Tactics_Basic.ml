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
          ((let uu____585 =
              let uu____588 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____588 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____585);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'Auu____675 . Prims.string -> 'Auu____675 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____686 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____686
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____691 . Prims.string -> Prims.string -> 'Auu____691 tac =
  fun msg  ->
    fun x  -> let uu____702 = FStar_Util.format1 msg x in fail uu____702
let fail2:
  'Auu____707 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____707 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____722 = FStar_Util.format2 msg x y in fail uu____722
let fail3:
  'Auu____728 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____728 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____747 = FStar_Util.format3 msg x y z in fail uu____747
let trytac': 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____777 = run t ps in
         match uu____777 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____798) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____823 = trytac' t in
    bind uu____823
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____850 -> ret FStar_Pervasives_Native.None)
let wrap_err: 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____876 = run t ps in
           match uu____876 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____893  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____906 =
          let uu____907 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck" in
          () in
        let debug_off uu____911 =
          let uu____912 = FStar_Options.set_options FStar_Options.Reset "" in
          () in
        (let uu____914 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346") in
         if uu____914
         then
           (debug_on ();
            (let uu____916 = FStar_Syntax_Print.term_to_string t1 in
             let uu____917 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____916
               uu____917))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2 in
           debug_off (); res
         with | uu____900_929 -> (debug_off (); false))
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____942 =
         let uu___61_943 = p in
         let uu____944 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___61_943.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___61_943.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___61_943.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____944;
           FStar_Tactics_Types.smt_goals =
             (uu___61_943.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___61_943.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___61_943.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___61_943.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___61_943.FStar_Tactics_Types.entry_range)
         } in
       set uu____942)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____957 = trysolve goal solution in
      if uu____957
      then dismiss
      else
        (let uu____961 =
           let uu____962 = tts goal.FStar_Tactics_Types.context solution in
           let uu____963 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____964 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____962 uu____963
             uu____964 in
         fail uu____961)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___62_971 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___62_971.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___62_971.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___62_971.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___62_971.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___62_971.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___62_971.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___62_971.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___62_971.FStar_Tactics_Types.entry_range)
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
      let uu____999 = FStar_TypeChecker_Env.pop_bv e in
      match uu____999 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____1017 =
      (let uu____1020 = aux b2 env in Prims.op_Negation uu____1020) &&
        (let uu____1022 = FStar_ST.op_Bang nwarn in
         uu____1022 < (Prims.parse_int "5")) in
    if uu____1017
    then
      ((let uu____1072 =
          let uu____1077 =
            let uu____1078 = goal_to_string g in
            FStar_Util.format1
              "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
              uu____1078 in
          (FStar_Errors.Warning_IllFormedGoal, uu____1077) in
        FStar_Errors.log_issue
          (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____1072);
       (let uu____1079 =
          let uu____1080 = FStar_ST.op_Bang nwarn in
          uu____1080 + (Prims.parse_int "1") in
        FStar_ST.op_Colon_Equals nwarn uu____1079))
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___63_1195 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___63_1195.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___63_1195.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___63_1195.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___63_1195.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___63_1195.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___63_1195.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___63_1195.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___63_1195.FStar_Tactics_Types.entry_range)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___64_1213 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___64_1213.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___64_1213.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___64_1213.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___64_1213.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___64_1213.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___64_1213.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___64_1213.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___64_1213.FStar_Tactics_Types.entry_range)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1231 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1231.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1231.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1231.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___65_1231.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1231.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1231.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1231.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1231.FStar_Tactics_Types.entry_range)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1249 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1249.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1249.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1249.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___66_1249.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___66_1249.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1249.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1249.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1249.FStar_Tactics_Types.entry_range)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1258  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___67_1270 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1270.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1270.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___67_1270.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___67_1270.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___67_1270.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1270.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1270.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1270.FStar_Tactics_Types.entry_range)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1296 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1296 with
        | (u,uu____1312,g_u) ->
            let uu____1326 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1326 (fun uu____1330  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1334 = FStar_Syntax_Util.un_squash t in
    match uu____1334 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1344 =
          let uu____1345 = FStar_Syntax_Subst.compress t' in
          uu____1345.FStar_Syntax_Syntax.n in
        (match uu____1344 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1349 -> false)
    | uu____1350 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1358 = FStar_Syntax_Util.un_squash t in
    match uu____1358 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1368 =
          let uu____1369 = FStar_Syntax_Subst.compress t' in
          uu____1369.FStar_Syntax_Syntax.n in
        (match uu____1368 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1373 -> false)
    | uu____1374 -> false
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
            let uu____1412 = env.FStar_TypeChecker_Env.universe_of env phi in
            FStar_Syntax_Util.mk_squash uu____1412 phi in
          let uu____1413 = new_uvar reason env typ in
          bind uu____1413
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
             let uu____1469 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1469
           with | e1 -> fail "not typeable")
let must_trivial: env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1517 =
          let uu____1518 =
            let uu____1519 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1519 in
          Prims.op_Negation uu____1518 in
        if uu____1517 then fail "got non-trivial guard" else ret ()
      with | uu____1528 -> fail "got non-trivial guard"
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1536 =
      bind cur_goal
        (fun goal  ->
           let uu____1542 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1542
             (fun uu____1562  ->
                match uu____1562 with
                | (t1,typ,guard) ->
                    let uu____1574 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____1574 (fun uu____1578  -> ret typ))) in
    FStar_All.pipe_left (wrap_err "tc") uu____1536
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1599 = mk_irrelevant_goal reason env phi opts in
          bind uu____1599 (fun goal  -> add_goals [goal])
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
       let uu____1619 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1619
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1623 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1623))
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
          let uu____1640 =
            let uu____1641 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1641.FStar_TypeChecker_Env.guard_f in
          match uu____1640 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1645 = istrivial e f in
              if uu____1645
              then ret ()
              else
                (let uu____1649 = mk_irrelevant_goal reason e f opts in
                 bind uu____1649
                   (fun goal  ->
                      let goal1 =
                        let uu___72_1656 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___72_1656.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___72_1656.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___72_1656.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___72_1656.FStar_Tactics_Types.opts);
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
          let uu____1677 =
            let uu____1678 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1678.FStar_TypeChecker_Env.guard_f in
          match uu____1677 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1686 = istrivial e f in
              if uu____1686
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1694 = mk_irrelevant_goal reason e f opts in
                 bind uu____1694
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___73_1704 = goal in
                            {
                              FStar_Tactics_Types.context =
                                (uu___73_1704.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___73_1704.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___73_1704.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___73_1704.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1710 = is_irrelevant g in
       if uu____1710
       then bind dismiss (fun uu____1714  -> add_smt_goals [g])
       else
         (let uu____1716 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1716))
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
             let uu____1757 =
               try
                 let uu____1791 =
                   let uu____1800 = FStar_BigInt.to_int_fs n1 in
                   FStar_List.splitAt uu____1800 p.FStar_Tactics_Types.goals in
                 ret uu____1791
               with | uu____1822 -> fail "divide: not enough goals" in
             bind uu____1757
               (fun uu____1849  ->
                  match uu____1849 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___74_1875 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___74_1875.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___74_1875.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___74_1875.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___74_1875.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___74_1875.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___74_1875.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___74_1875.FStar_Tactics_Types.entry_range)
                        } in
                      let rp =
                        let uu___75_1877 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___75_1877.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___75_1877.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___75_1877.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___75_1877.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___75_1877.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___75_1877.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___75_1877.FStar_Tactics_Types.entry_range)
                        } in
                      let uu____1878 = set lp in
                      bind uu____1878
                        (fun uu____1886  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1900 = set rp in
                                     bind uu____1900
                                       (fun uu____1908  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___76_1924 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___76_1924.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___76_1924.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___76_1924.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___76_1924.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___76_1924.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___76_1924.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___76_1924.FStar_Tactics_Types.entry_range)
                                                      } in
                                                    let uu____1925 = set p' in
                                                    bind uu____1925
                                                      (fun uu____1933  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1951 = divide FStar_BigInt.one f idtac in
    bind uu____1951
      (fun uu____1964  -> match uu____1964 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1998::uu____1999 ->
             let uu____2002 =
               let uu____2011 = map tau in
               divide FStar_BigInt.one tau uu____2011 in
             bind uu____2002
               (fun uu____2029  ->
                  match uu____2029 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____2066 =
        bind t1
          (fun uu____2071  ->
             let uu____2072 = map t2 in
             bind uu____2072 (fun uu____2080  -> ret ())) in
      focus uu____2066
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____2091 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____2091 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2106 =
             let uu____2107 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____2107 in
           if uu____2106
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____2113 = new_uvar "intro" env' typ' in
              bind uu____2113
                (fun u  ->
                   let uu____2120 =
                     let uu____2121 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____2121 in
                   if uu____2120
                   then
                     let uu____2124 =
                       let uu____2127 =
                         let uu___79_2128 = goal in
                         let uu____2129 = bnorm env' u in
                         let uu____2130 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2129;
                           FStar_Tactics_Types.goal_ty = uu____2130;
                           FStar_Tactics_Types.opts =
                             (uu___79_2128.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___79_2128.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____2127 in
                     bind uu____2124 (fun uu____2132  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2138 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____2138)
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
       (let uu____2159 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____2159 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2178 =
              let uu____2179 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____2179 in
            if uu____2178
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____2195 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____2195; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____2197 =
                 let uu____2200 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____2200 in
               bind uu____2197
                 (fun u  ->
                    let lb =
                      let uu____2216 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2216 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2220 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2220 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2257 =
                            let uu____2260 =
                              let uu___80_2261 = goal in
                              let uu____2262 = bnorm env' u in
                              let uu____2263 =
                                let uu____2264 = comp_to_typ c in
                                bnorm env' uu____2264 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2262;
                                FStar_Tactics_Types.goal_ty = uu____2263;
                                FStar_Tactics_Types.opts =
                                  (uu___80_2261.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___80_2261.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2260 in
                          bind uu____2257
                            (fun uu____2271  ->
                               let uu____2272 =
                                 let uu____2277 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2277, b) in
                               ret uu____2272)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2291 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2291))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2315 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2315 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___81_2322 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___81_2322.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___81_2322.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___81_2322.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2340 =
          bind get
            (fun ps  ->
               let uu____2346 = __tc e t in
               bind uu____2346
                 (fun uu____2368  ->
                    match uu____2368 with
                    | (t1,uu____2378,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2384 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2384 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2340
let refine_intro: Prims.unit tac =
  let uu____2394 =
    bind cur_goal
      (fun g  ->
         let uu____2401 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
         match uu____2401 with
         | (uu____2414,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___82_2439 = g in
               {
                 FStar_Tactics_Types.context =
                   (uu___82_2439.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___82_2439.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___82_2439.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___82_2439.FStar_Tactics_Types.is_guard)
               } in
             let uu____2440 =
               let uu____2445 =
                 let uu____2450 =
                   let uu____2451 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2451] in
                 FStar_Syntax_Subst.open_term uu____2450 phi in
               match uu____2445 with
               | (bvs,phi1) ->
                   let uu____2458 =
                     let uu____2459 = FStar_List.hd bvs in
                     FStar_Pervasives_Native.fst uu____2459 in
                   (uu____2458, phi1) in
             (match uu____2440 with
              | (bv1,phi1) ->
                  let uu____2472 =
                    let uu____2475 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1 in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2475
                      g.FStar_Tactics_Types.opts in
                  bind uu____2472
                    (fun g2  ->
                       bind dismiss (fun uu____2479  -> add_goals [g1; g2])))) in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2394
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
             let uu____2503 = __tc env t in
             bind uu____2503
               (fun uu____2523  ->
                  match uu____2523 with
                  | (t1,typ,guard) ->
                      let uu____2535 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts in
                      bind uu____2535
                        (fun uu____2542  ->
                           mlog
                             (fun uu____2546  ->
                                let uu____2547 =
                                  tts goal.FStar_Tactics_Types.context typ in
                                let uu____2548 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2547
                                  uu____2548)
                             (fun uu____2551  ->
                                let uu____2552 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty in
                                if uu____2552
                                then solve goal t1
                                else
                                  (let uu____2556 =
                                     tts goal.FStar_Tactics_Types.context t1 in
                                   let uu____2557 =
                                     tts goal.FStar_Tactics_Types.context typ in
                                   let uu____2558 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty in
                                   fail3
                                     "%s : %s does not exactly solve the goal %s"
                                     uu____2556 uu____2557 uu____2558)))))
let t_exact:
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2572 =
          mlog
            (fun uu____2577  ->
               let uu____2578 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "exact: tm = %s\n" uu____2578)
            (fun uu____2581  ->
               let uu____2582 =
                 let uu____2589 =
                   __exact_now set_expected_typ1 force_guard tm in
                 trytac' uu____2589 in
               bind uu____2582
                 (fun uu___56_2598  ->
                    match uu___56_2598 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2607 =
                          let uu____2614 =
                            let uu____2617 =
                              norm [FStar_Syntax_Embeddings.Delta] in
                            bind uu____2617
                              (fun uu____2621  ->
                                 bind refine_intro
                                   (fun uu____2623  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm)) in
                          trytac' uu____2614 in
                        bind uu____2607
                          (fun uu___55_2630  ->
                             match uu___55_2630 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2638 -> fail e))) in
        FStar_All.pipe_left (wrap_err "exact") uu____2572
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2653 =
             let uu____2660 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2660 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2653 in
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
          let uu____2720 = f x in
          bind uu____2720
            (fun y  ->
               let uu____2728 = mapM f xs in
               bind uu____2728 (fun ys  -> ret (y :: ys)))
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2746 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2763 =
               let uu____2768 = t_exact false true tm in trytac uu____2768 in
             bind uu____2763
               (fun uu___57_2775  ->
                  match uu___57_2775 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2781 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2781 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2813  ->
                                let uu____2814 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2814)
                             (fun uu____2817  ->
                                let uu____2818 =
                                  let uu____2819 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2819 in
                                if uu____2818
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2823 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2823
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2843 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2843 in
                                        let uu____2844 =
                                          __apply uopt tm' typ' in
                                        bind uu____2844
                                          (fun uu____2852  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2854 =
                                               let uu____2855 =
                                                 let uu____2858 =
                                                   let uu____2859 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2859 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2858 in
                                               uu____2855.FStar_Syntax_Syntax.n in
                                             match uu____2854 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2887) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2915 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2915
                                                      then ret ()
                                                      else
                                                        (let uu____2919 =
                                                           let uu____2922 =
                                                             let uu___83_2923
                                                               = goal in
                                                             let uu____2924 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2925 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___83_2923.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2924;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2925;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___83_2923.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2922] in
                                                         add_goals uu____2919))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2971 =
        mlog
          (fun uu____2976  ->
             let uu____2977 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2977)
          (fun uu____2979  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2983 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2983
                    (fun uu____3004  ->
                       match uu____3004 with
                       | (tm1,typ,guard) ->
                           let uu____3016 =
                             let uu____3019 =
                               let uu____3022 = __apply uopt tm1 typ in
                               bind uu____3022
                                 (fun uu____3026  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____3019 in
                           let uu____3027 =
                             let uu____3030 =
                               tts goal.FStar_Tactics_Types.context tm1 in
                             let uu____3031 =
                               tts goal.FStar_Tactics_Types.context typ in
                             let uu____3032 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3030 uu____3031 uu____3032 in
                           try_unif uu____3016 uu____3027))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2971
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____3044 =
      let uu____3047 =
        mlog
          (fun uu____3052  ->
             let uu____3053 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3053)
          (fun uu____3056  ->
             let is_unit_t t =
               let uu____3061 =
                 let uu____3062 = FStar_Syntax_Subst.compress t in
                 uu____3062.FStar_Syntax_Syntax.n in
               match uu____3061 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3066 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____3070 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____3070
                    (fun uu____3092  ->
                       match uu____3092 with
                       | (tm1,t,guard) ->
                           let uu____3104 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____3104 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3134 =
                                     FStar_List.fold_left
                                       (fun uu____3180  ->
                                          fun uu____3181  ->
                                            match (uu____3180, uu____3181)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____3284 =
                                                  is_unit_t b_t in
                                                if uu____3284
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3322 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____3322 with
                                                   | (u,uu____3352,g_u) ->
                                                       let uu____3366 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____3366,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____3134 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3436 =
                                         let uu____3445 =
                                           let uu____3454 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3454.FStar_Syntax_Syntax.effect_args in
                                         match uu____3445 with
                                         | pre::post::uu____3465 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3506 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3436 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3538 =
                                                let uu____3547 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3547] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3538 in
                                            let uu____3548 =
                                              let uu____3549 =
                                                let uu____3550 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3550
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3549 in
                                            if uu____3548
                                            then
                                              let uu____3553 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3554 =
                                                let uu____3555 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1 in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3555 in
                                              let uu____3556 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3553 uu____3554
                                                uu____3556
                                            else
                                              (let solution =
                                                 let uu____3559 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3559 in
                                               let uu____3560 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3560
                                                 (fun uu____3565  ->
                                                    let uu____3566 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit in
                                                    bind uu____3566
                                                      (fun uu____3574  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3585 =
                                                               let uu____3592
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3592 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3585 in
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
                                                           let uu____3633 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3633
                                                           with
                                                           | (hd1,uu____3649)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3671)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3696
                                                                    -> false) in
                                                         let uu____3697 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3769
                                                                    ->
                                                                   match uu____3769
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3797)
                                                                    ->
                                                                    let uu____3798
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____3798
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3824)
                                                                    ->
                                                                    let uu____3845
                                                                    =
                                                                    let uu____3846
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3846.FStar_Syntax_Syntax.n in
                                                                    (match uu____3845
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3859
                                                                    ->
                                                                    let uu____3876
                                                                    =
                                                                    let uu____3885
                                                                    =
                                                                    let uu____3888
                                                                    =
                                                                    let uu___86_3889
                                                                    = goal in
                                                                    let uu____3890
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3891
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___86_3889.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3890;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3891;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___86_3889.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___86_3889.FStar_Tactics_Types.is_guard)
                                                                    } in
                                                                    [uu____3888] in
                                                                    (uu____3885,
                                                                    []) in
                                                                    ret
                                                                    uu____3876
                                                                    | 
                                                                    uu____3904
                                                                    ->
                                                                    let term1
                                                                    =
                                                                    bnorm env
                                                                    term in
                                                                    let uu____3906
                                                                    =
                                                                    let uu____3913
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3913
                                                                    term1 in
                                                                    (match uu____3906
                                                                    with
                                                                    | 
                                                                    (uu____3924,uu____3925,g_typ)
                                                                    ->
                                                                    let uu____3927
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts in
                                                                    bind
                                                                    uu____3927
                                                                    (fun
                                                                    uu___58_3943
                                                                     ->
                                                                    match uu___58_3943
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
                                                         bind uu____3697
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____4011
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____4011 in
                                                              let smt_goals =
                                                                let uu____4033
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____4033 in
                                                              let rec filter'
                                                                f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4089
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____4089
                                                                    then
                                                                    let uu____4092
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____4092
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                              let sub_goals1
                                                                =
                                                                filter'
                                                                  (fun g  ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4106
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____4106)
                                                                  sub_goals in
                                                              let uu____4107
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts in
                                                              bind uu____4107
                                                                (fun
                                                                   uu____4112
                                                                    ->
                                                                   let uu____4113
                                                                    =
                                                                    let uu____4116
                                                                    =
                                                                    let uu____4117
                                                                    =
                                                                    let uu____4118
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4118 in
                                                                    Prims.op_Negation
                                                                    uu____4117 in
                                                                    if
                                                                    uu____4116
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret () in
                                                                   bind
                                                                    uu____4113
                                                                    (fun
                                                                    uu____4124
                                                                     ->
                                                                    let uu____4125
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals in
                                                                    bind
                                                                    uu____4125
                                                                    (fun
                                                                    uu____4129
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))) in
      focus uu____3047 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3044
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4149 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____4149 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4159::(e1,uu____4161)::(e2,uu____4163)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4222 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4244 = destruct_eq' typ in
    match uu____4244 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4274 = FStar_Syntax_Util.un_squash typ in
        (match uu____4274 with
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
        let uu____4330 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____4330 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4378 = aux e' in
               FStar_Util.map_opt uu____4378
                 (fun uu____4402  ->
                    match uu____4402 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____4423 = aux e in
      FStar_Util.map_opt uu____4423
        (fun uu____4447  ->
           match uu____4447 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____4502 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____4502
            (fun uu____4526  ->
               match uu____4526 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___87_4543 = bv in
                     let uu____4544 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___87_4543.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___87_4543.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4544
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___88_4553 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___88_4553.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___88_4553.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4566 = h in
         match uu____4566 with
         | (bv,uu____4570) ->
             mlog
               (fun uu____4574  ->
                  let uu____4575 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4576 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4575
                    uu____4576)
               (fun uu____4579  ->
                  let uu____4580 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4580 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4609 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4609 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4624 =
                             let uu____4625 = FStar_Syntax_Subst.compress x in
                             uu____4625.FStar_Syntax_Syntax.n in
                           (match uu____4624 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___89_4638 = bv1 in
                                  let uu____4639 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___89_4638.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___89_4638.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4639
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4645 =
                                  let uu___90_4646 = goal in
                                  let uu____4647 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4648 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4649 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4647;
                                    FStar_Tactics_Types.witness = uu____4648;
                                    FStar_Tactics_Types.goal_ty = uu____4649;
                                    FStar_Tactics_Types.opts =
                                      (uu___90_4646.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___90_4646.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4645
                            | uu____4650 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4651 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4676 = b in
           match uu____4676 with
           | (bv,uu____4680) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___91_4684 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___91_4684.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___91_4684.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4688 =
                   let uu____4689 =
                     let uu____4696 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4696) in
                   FStar_Syntax_Syntax.NT uu____4689 in
                 [uu____4688] in
               let uu____4697 = subst_goal bv bv' s1 goal in
               (match uu____4697 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4716 = b in
         match uu____4716 with
         | (bv,uu____4720) ->
             let uu____4721 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4721 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4750 = FStar_Syntax_Util.type_u () in
                  (match uu____4750 with
                   | (ty,u) ->
                       let uu____4759 = new_uvar "binder_retype" e0 ty in
                       bind uu____4759
                         (fun t'  ->
                            let bv'' =
                              let uu___92_4769 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___92_4769.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___92_4769.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4773 =
                                let uu____4774 =
                                  let uu____4781 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4781) in
                                FStar_Syntax_Syntax.NT uu____4774 in
                              [uu____4773] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___93_4789 = b1 in
                                   let uu____4790 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___93_4789.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___93_4789.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4790
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4796  ->
                                 let uu____4797 =
                                   let uu____4800 =
                                     let uu____4803 =
                                       let uu___94_4804 = goal in
                                       let uu____4805 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4806 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4805;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4806;
                                         FStar_Tactics_Types.opts =
                                           (uu___94_4804.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___94_4804.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4803] in
                                   add_goals uu____4800 in
                                 bind uu____4797
                                   (fun uu____4809  ->
                                      let uu____4810 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4810
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4831 = b in
           match uu____4831 with
           | (bv,uu____4835) ->
               let uu____4836 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4836 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4868 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4868 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___95_4873 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___95_4873.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___95_4873.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___96_4877 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___96_4877.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___96_4877.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___96_4877.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___96_4877.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4883 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4883 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4905 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4905 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___97_4939 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___97_4939.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___97_4939.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4950 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4950 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4971 = FStar_Syntax_Print.bv_to_string x in
               let uu____4972 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4971 uu____4972
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4979 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4979 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____5001 = FStar_Util.set_mem x fns_ty in
           if uu____5001
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____5005 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____5005
                (fun u  ->
                   let uu____5011 =
                     let uu____5012 = trysolve goal u in
                     Prims.op_Negation uu____5012 in
                   if uu____5011
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___98_5017 = goal in
                        let uu____5018 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____5018;
                          FStar_Tactics_Types.goal_ty =
                            (uu___98_5017.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___98_5017.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___98_5017.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____5020  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____5031 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____5031 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____5055  ->
                    let uu____5056 = clear b in
                    bind uu____5056
                      (fun uu____5060  ->
                         bind intro (fun uu____5062  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___99_5078 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___99_5078.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___99_5078.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___99_5078.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___99_5078.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5080  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___100_5096 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___100_5096.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___100_5096.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___100_5096.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___100_5096.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5098  -> add_goals [g']))
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
            let uu____5130 = FStar_Syntax_Subst.compress t in
            uu____5130.FStar_Syntax_Syntax.n in
          let uu____5133 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___102_5139 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___102_5139.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___102_5139.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____5133
            (fun t1  ->
               let tn1 =
                 let uu____5147 =
                   let uu____5148 = FStar_Syntax_Subst.compress t1 in
                   uu____5148.FStar_Syntax_Syntax.n in
                 match uu____5147 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____5180 = ff hd1 in
                     bind uu____5180
                       (fun hd2  ->
                          let fa uu____5200 =
                            match uu____5200 with
                            | (a,q) ->
                                let uu____5213 = ff a in
                                bind uu____5213 (fun a1  -> ret (a1, q)) in
                          let uu____5226 = mapM fa args in
                          bind uu____5226
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5286 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____5286 with
                      | (bs1,t') ->
                          let uu____5295 =
                            let uu____5298 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____5298 t' in
                          bind uu____5295
                            (fun t''  ->
                               let uu____5302 =
                                 let uu____5303 =
                                   let uu____5320 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____5321 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____5320, uu____5321, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____5303 in
                               ret uu____5302))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5342 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___101_5349 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___101_5349.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___101_5349.FStar_Syntax_Syntax.vars)
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
            let uu____5378 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____5378 with
            | (t1,lcomp,g) ->
                let uu____5390 =
                  (let uu____5393 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____5393) ||
                    (let uu____5395 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____5395) in
                if uu____5390
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____5405 = new_uvar "pointwise_rec" env typ in
                     bind uu____5405
                       (fun ut  ->
                          log ps
                            (fun uu____5416  ->
                               let uu____5417 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____5418 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5417 uu____5418);
                          (let uu____5419 =
                             let uu____5422 =
                               let uu____5423 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____5423 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5422 opts in
                           bind uu____5419
                             (fun uu____5426  ->
                                let uu____5427 =
                                  bind tau
                                    (fun uu____5433  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____5439  ->
                                            let uu____5440 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____5441 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5440 uu____5441);
                                       ret ut1) in
                                focus uu____5427))) in
                   let uu____5442 = trytac' rewrite_eq in
                   bind uu____5442
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
           let uu____5484 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5484 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5521  ->
                     let uu____5522 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5522);
                bind dismiss_all
                  (fun uu____5525  ->
                     let uu____5526 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5526
                       (fun gt'  ->
                          log ps
                            (fun uu____5536  ->
                               let uu____5537 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5537);
                          (let uu____5538 = push_goals gs in
                           bind uu____5538
                             (fun uu____5542  ->
                                add_goals
                                  [(let uu___103_5544 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___103_5544.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___103_5544.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___103_5544.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___103_5544.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5564 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5564 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5576 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5576 with
            | (hd1,args) ->
                let uu____5609 =
                  let uu____5622 =
                    let uu____5623 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5623.FStar_Syntax_Syntax.n in
                  (uu____5622, args) in
                (match uu____5609 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5637::(l,uu____5639)::(r,uu____5641)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5688 =
                       let uu____5689 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5689 in
                     if uu____5688
                     then
                       let uu____5692 = tts g.FStar_Tactics_Types.context l in
                       let uu____5693 = tts g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5692 uu____5693
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5696) ->
                     let uu____5713 = tts g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5713))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5721 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5721
         (fun u  ->
            let g' =
              let uu___104_5728 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___104_5728.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___104_5728.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___104_5728.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___104_5728.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5731  ->
                 let uu____5732 =
                   let uu____5735 =
                     let uu____5736 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5736
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5735
                     g.FStar_Tactics_Types.opts in
                 bind uu____5732
                   (fun uu____5739  ->
                      let uu____5740 = add_goals [g'] in
                      bind uu____5740 (fun uu____5744  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___105_5761 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___105_5761.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___105_5761.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___105_5761.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___105_5761.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___105_5761.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___105_5761.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___105_5761.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___105_5761.FStar_Tactics_Types.entry_range)
              })
       | uu____5762 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___106_5777 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___106_5777.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___106_5777.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___106_5777.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___106_5777.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___106_5777.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___106_5777.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___106_5777.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___106_5777.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5784 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5802 =
      bind cur_goal
        (fun g  ->
           let uu____5816 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5816
             (fun uu____5852  ->
                match uu____5852 with
                | (t1,typ,guard) ->
                    let uu____5868 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5868 with
                     | (hd1,args) ->
                         let uu____5911 =
                           let uu____5924 =
                             let uu____5925 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5925.FStar_Syntax_Syntax.n in
                           (uu____5924, args) in
                         (match uu____5911 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5944)::(q,uu____5946)::[]) when
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
                                let uu___107_5984 = g in
                                let uu____5985 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5985;
                                  FStar_Tactics_Types.witness =
                                    (uu___107_5984.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___107_5984.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___107_5984.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___107_5984.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___108_5987 = g in
                                let uu____5988 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5988;
                                  FStar_Tactics_Types.witness =
                                    (uu___108_5987.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___108_5987.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___108_5987.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___108_5987.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5995  ->
                                   let uu____5996 = add_goals [g1; g2] in
                                   bind uu____5996
                                     (fun uu____6005  ->
                                        let uu____6006 =
                                          let uu____6011 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____6012 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____6011, uu____6012) in
                                        ret uu____6006))
                          | uu____6017 ->
                              let uu____6030 =
                                tts g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____6030)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5802
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6068 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____6068);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___109_6075 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___109_6075.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___109_6075.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___109_6075.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___109_6075.FStar_Tactics_Types.is_guard)
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
      let uu____6111 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____6119 = __tc env tm in
             bind uu____6119
               (fun uu____6139  ->
                  match uu____6139 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____6111
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____6170 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6176 =
              let uu____6177 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6177 in
            new_uvar "uvar_env.2" env uu____6176 in
      bind uu____6170
        (fun typ  ->
           let uu____6189 = new_uvar "uvar_env" env typ in
           bind uu____6189 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____6201 =
      bind cur_goal
        (fun goal  ->
           let uu____6207 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____6207
             (fun uu____6227  ->
                match uu____6227 with
                | (t1,typ,guard) ->
                    let uu____6239 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____6239
                      (fun uu____6244  ->
                         let uu____6245 =
                           let uu____6248 =
                             let uu___110_6249 = goal in
                             let uu____6250 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____6251 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___110_6249.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6250;
                               FStar_Tactics_Types.goal_ty = uu____6251;
                               FStar_Tactics_Types.opts =
                                 (uu___110_6249.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____6248] in
                         add_goals uu____6245))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6201
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6269 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____6269)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6286  ->
             let uu____6287 = FStar_Options.unsafe_tactic_exec () in
             if uu____6287
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6293  -> fun uu____6294  -> false) in
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
      let uu____6314 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____6314 with
      | (u,uu____6332,g_u) ->
          let g =
            let uu____6347 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6347;
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
      let uu____6362 = goal_of_goal_ty env typ in
      match uu____6362 with
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