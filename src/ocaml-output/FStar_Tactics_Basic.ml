open Prims
type goal = FStar_Tactics_Types.goal[@@deriving show]
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
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
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
      let uu____531 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____531 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____558 =
              let uu____561 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____561 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____558);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____630 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____630
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____635 . Prims.string -> Prims.string -> 'Auu____635 tac =
  fun msg  ->
    fun x  -> let uu____646 = FStar_Util.format1 msg x in fail uu____646
let fail2:
  'Auu____651 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____651 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____666 = FStar_Util.format2 msg x y in fail uu____666
let fail3:
  'Auu____672 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____672 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____691 = FStar_Util.format3 msg x y z in fail uu____691
let fail4:
  'Auu____698 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____698 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____721 = FStar_Util.format4 msg x y z w in fail uu____721
let trytac': 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____751 = run t ps in
         match uu____751 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____772) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____797 = trytac' t in
    bind uu____797
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____824 -> ret FStar_Pervasives_Native.None)
let wrap_err: 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____850 = run t ps in
           match uu____850 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____867  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____880 =
          let uu____881 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck" in
          () in
        let debug_off uu____885 =
          let uu____886 = FStar_Options.set_options FStar_Options.Reset "" in
          () in
        (let uu____888 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346") in
         if uu____888
         then
           (debug_on ();
            (let uu____890 = FStar_Syntax_Print.term_to_string t1 in
             let uu____891 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____890
               uu____891))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2 in
           debug_off (); res
         with | uu____903 -> (debug_off (); false))
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____916 =
         let uu___63_917 = p in
         let uu____918 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___63_917.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___63_917.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___63_917.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____918;
           FStar_Tactics_Types.smt_goals =
             (uu___63_917.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___63_917.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___63_917.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___63_917.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___63_917.FStar_Tactics_Types.entry_range)
         } in
       set uu____916)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____931 = trysolve goal solution in
      if uu____931
      then dismiss
      else
        (let uu____935 =
           let uu____936 = tts goal.FStar_Tactics_Types.context solution in
           let uu____937 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____938 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____936 uu____937
             uu____938 in
         fail uu____935)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___64_945 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___64_945.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___64_945.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___64_945.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___64_945.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___64_945.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___64_945.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___64_945.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___64_945.FStar_Tactics_Types.entry_range)
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
      let uu____973 = FStar_TypeChecker_Env.pop_bv e in
      match uu____973 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____991 =
      (let uu____994 = aux b2 env in Prims.op_Negation uu____994) &&
        (let uu____996 = FStar_ST.op_Bang nwarn in
         uu____996 < (Prims.parse_int "5")) in
    if uu____991
    then
      ((let uu____1017 =
          let uu____1022 =
            let uu____1023 = goal_to_string g in
            FStar_Util.format1
              "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
              uu____1023 in
          (FStar_Errors.Warning_IllFormedGoal, uu____1022) in
        FStar_Errors.log_issue
          (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____1017);
       (let uu____1024 =
          let uu____1025 = FStar_ST.op_Bang nwarn in
          uu____1025 + (Prims.parse_int "1") in
        FStar_ST.op_Colon_Equals nwarn uu____1024))
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1082 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1082.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1082.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1082.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___65_1082.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1082.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1082.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1082.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1082.FStar_Tactics_Types.entry_range)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1100 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1100.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1100.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1100.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___66_1100.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___66_1100.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1100.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1100.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1100.FStar_Tactics_Types.entry_range)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___67_1118 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1118.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1118.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___67_1118.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___67_1118.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___67_1118.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1118.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1118.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1118.FStar_Tactics_Types.entry_range)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___68_1136 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___68_1136.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___68_1136.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___68_1136.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___68_1136.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___68_1136.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___68_1136.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___68_1136.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___68_1136.FStar_Tactics_Types.entry_range)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1145  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___69_1157 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___69_1157.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___69_1157.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___69_1157.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___69_1157.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___69_1157.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___69_1157.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___69_1157.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___69_1157.FStar_Tactics_Types.entry_range)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1183 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1183 with
        | (u,uu____1199,g_u) ->
            let uu____1213 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1213 (fun uu____1217  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1221 = FStar_Syntax_Util.un_squash t in
    match uu____1221 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1231 =
          let uu____1232 = FStar_Syntax_Subst.compress t' in
          uu____1232.FStar_Syntax_Syntax.n in
        (match uu____1231 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1236 -> false)
    | uu____1237 -> false
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
            let uu____1301 = env.FStar_TypeChecker_Env.universe_of env phi in
            FStar_Syntax_Util.mk_squash uu____1301 phi in
          let uu____1302 = new_uvar reason env typ in
          bind uu____1302
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
             let uu____1358 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1358
           with | e1 -> fail "not typeable")
let must_trivial: env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1406 =
          let uu____1407 =
            let uu____1408 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1408 in
          Prims.op_Negation uu____1407 in
        if uu____1406 then fail "got non-trivial guard" else ret ()
      with | uu____1417 -> fail "got non-trivial guard"
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1425 =
      bind cur_goal
        (fun goal  ->
           let uu____1431 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1431
             (fun uu____1451  ->
                match uu____1451 with
                | (t1,typ,guard) ->
                    let uu____1463 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____1463 (fun uu____1467  -> ret typ))) in
    FStar_All.pipe_left (wrap_err "tc") uu____1425
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1488 = mk_irrelevant_goal reason env phi opts in
          bind uu____1488 (fun goal  -> add_goals [goal])
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
       let uu____1510 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1510
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1514 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1514))
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
          let uu____1531 =
            let uu____1532 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1532.FStar_TypeChecker_Env.guard_f in
          match uu____1531 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1536 = istrivial e f in
              if uu____1536
              then ret ()
              else
                (let uu____1540 = mk_irrelevant_goal reason e f opts in
                 bind uu____1540
                   (fun goal  ->
                      let goal1 =
                        let uu___74_1547 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___74_1547.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___74_1547.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___74_1547.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___74_1547.FStar_Tactics_Types.opts);
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
          let uu____1568 =
            let uu____1569 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1569.FStar_TypeChecker_Env.guard_f in
          match uu____1568 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1577 = istrivial e f in
              if uu____1577
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1585 = mk_irrelevant_goal reason e f opts in
                 bind uu____1585
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___75_1595 = goal in
                            {
                              FStar_Tactics_Types.context =
                                (uu___75_1595.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___75_1595.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___75_1595.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___75_1595.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1603 = is_irrelevant g in
       if uu____1603
       then bind dismiss (fun uu____1607  -> add_smt_goals [g])
       else
         (let uu____1609 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1609))
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
             let uu____1650 =
               try
                 let uu____1684 =
                   let uu____1693 = FStar_BigInt.to_int_fs n1 in
                   FStar_List.splitAt uu____1693 p.FStar_Tactics_Types.goals in
                 ret uu____1684
               with | uu____1715 -> fail "divide: not enough goals" in
             bind uu____1650
               (fun uu____1742  ->
                  match uu____1742 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___76_1768 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___76_1768.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___76_1768.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___76_1768.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___76_1768.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___76_1768.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___76_1768.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___76_1768.FStar_Tactics_Types.entry_range)
                        } in
                      let rp =
                        let uu___77_1770 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___77_1770.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___77_1770.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___77_1770.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___77_1770.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___77_1770.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___77_1770.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___77_1770.FStar_Tactics_Types.entry_range)
                        } in
                      let uu____1771 = set lp in
                      bind uu____1771
                        (fun uu____1779  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1793 = set rp in
                                     bind uu____1793
                                       (fun uu____1801  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___78_1817 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___78_1817.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___78_1817.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___78_1817.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___78_1817.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___78_1817.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___78_1817.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___78_1817.FStar_Tactics_Types.entry_range)
                                                      } in
                                                    let uu____1818 = set p' in
                                                    bind uu____1818
                                                      (fun uu____1826  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1844 = divide FStar_BigInt.one f idtac in
    bind uu____1844
      (fun uu____1857  -> match uu____1857 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1891::uu____1892 ->
             let uu____1895 =
               let uu____1904 = map tau in
               divide FStar_BigInt.one tau uu____1904 in
             bind uu____1895
               (fun uu____1922  ->
                  match uu____1922 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1959 =
        bind t1
          (fun uu____1964  ->
             let uu____1965 = map t2 in
             bind uu____1965 (fun uu____1973  -> ret ())) in
      focus uu____1959
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1986 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1986 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2001 =
             let uu____2002 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____2002 in
           if uu____2001
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____2008 = new_uvar "intro" env' typ' in
              bind uu____2008
                (fun u  ->
                   let uu____2015 =
                     let uu____2016 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____2016 in
                   if uu____2015
                   then
                     let uu____2019 =
                       let uu____2022 =
                         let uu___81_2023 = goal in
                         let uu____2024 = bnorm env' u in
                         let uu____2025 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2024;
                           FStar_Tactics_Types.goal_ty = uu____2025;
                           FStar_Tactics_Types.opts =
                             (uu___81_2023.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___81_2023.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____2022 in
                     bind uu____2019 (fun uu____2027  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2033 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____2033)
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
       (let uu____2060 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____2060 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2079 =
              let uu____2080 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____2080 in
            if uu____2079
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____2096 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____2096; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____2098 =
                 let uu____2101 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____2101 in
               bind uu____2098
                 (fun u  ->
                    let lb =
                      let uu____2117 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2117 [] in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2123 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2123 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2160 =
                            let uu____2163 =
                              let uu___82_2164 = goal in
                              let uu____2165 = bnorm env' u in
                              let uu____2166 =
                                let uu____2167 = comp_to_typ c in
                                bnorm env' uu____2167 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2165;
                                FStar_Tactics_Types.goal_ty = uu____2166;
                                FStar_Tactics_Types.opts =
                                  (uu___82_2164.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___82_2164.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2163 in
                          bind uu____2160
                            (fun uu____2174  ->
                               let uu____2175 =
                                 let uu____2180 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2180, b) in
                               ret uu____2175)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2194 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2194))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2214  ->
              let uu____2215 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness in
              FStar_Util.print1 "norm: witness = %s\n" uu____2215)
           (fun uu____2220  ->
              let steps =
                let uu____2224 = FStar_TypeChecker_Normalize.tr_norm_steps s in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2224 in
              let w =
                normalize steps goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.witness in
              let t =
                normalize steps goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty in
              replace_cur
                (let uu___83_2231 = goal in
                 {
                   FStar_Tactics_Types.context =
                     (uu___83_2231.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___83_2231.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___83_2231.FStar_Tactics_Types.is_guard)
                 })))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2249 =
          mlog
            (fun uu____2254  ->
               let uu____2255 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2255)
            (fun uu____2257  ->
               bind get
                 (fun ps  ->
                    let uu____2261 = __tc e t in
                    bind uu____2261
                      (fun uu____2283  ->
                         match uu____2283 with
                         | (t1,uu____2293,guard) ->
                             (FStar_TypeChecker_Rel.force_trivial_guard e
                                guard;
                              (let steps =
                                 let uu____2299 =
                                   FStar_TypeChecker_Normalize.tr_norm_steps
                                     s in
                                 FStar_List.append
                                   [FStar_TypeChecker_Normalize.Reify;
                                   FStar_TypeChecker_Normalize.UnfoldTac]
                                   uu____2299 in
                               let t2 =
                                 normalize steps
                                   ps.FStar_Tactics_Types.main_context t1 in
                               ret t2))))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2249
let refine_intro: Prims.unit tac =
  let uu____2311 =
    bind cur_goal
      (fun g  ->
         let uu____2318 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
         match uu____2318 with
         | (uu____2331,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___84_2356 = g in
               {
                 FStar_Tactics_Types.context =
                   (uu___84_2356.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___84_2356.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___84_2356.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___84_2356.FStar_Tactics_Types.is_guard)
               } in
             let uu____2357 =
               let uu____2362 =
                 let uu____2367 =
                   let uu____2368 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2368] in
                 FStar_Syntax_Subst.open_term uu____2367 phi in
               match uu____2362 with
               | (bvs,phi1) ->
                   let uu____2375 =
                     let uu____2376 = FStar_List.hd bvs in
                     FStar_Pervasives_Native.fst uu____2376 in
                   (uu____2375, phi1) in
             (match uu____2357 with
              | (bv1,phi1) ->
                  let uu____2389 =
                    let uu____2392 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1 in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2392
                      g.FStar_Tactics_Types.opts in
                  bind uu____2389
                    (fun g2  ->
                       bind dismiss (fun uu____2396  -> add_goals [g1; g2])))) in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2311
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
             let uu____2420 = __tc env t in
             bind uu____2420
               (fun uu____2440  ->
                  match uu____2440 with
                  | (t1,typ,guard) ->
                      let uu____2452 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts in
                      bind uu____2452
                        (fun uu____2459  ->
                           mlog
                             (fun uu____2463  ->
                                let uu____2464 =
                                  tts goal.FStar_Tactics_Types.context typ in
                                let uu____2465 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2464
                                  uu____2465)
                             (fun uu____2468  ->
                                let uu____2469 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty in
                                if uu____2469
                                then solve goal t1
                                else
                                  (let uu____2473 =
                                     tts goal.FStar_Tactics_Types.context t1 in
                                   let uu____2474 =
                                     tts goal.FStar_Tactics_Types.context typ in
                                   let uu____2475 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty in
                                   let uu____2476 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.witness in
                                   fail4
                                     "%s : %s does not exactly solve the goal %s (witness = %s)"
                                     uu____2473 uu____2474 uu____2475
                                     uu____2476)))))
let t_exact:
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2490 =
          mlog
            (fun uu____2495  ->
               let uu____2496 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____2496)
            (fun uu____2499  ->
               let uu____2500 =
                 let uu____2507 =
                   __exact_now set_expected_typ1 force_guard tm in
                 trytac' uu____2507 in
               bind uu____2500
                 (fun uu___58_2516  ->
                    match uu___58_2516 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2525 =
                          let uu____2532 =
                            let uu____2535 =
                              norm [FStar_Syntax_Embeddings.Delta] in
                            bind uu____2535
                              (fun uu____2539  ->
                                 bind refine_intro
                                   (fun uu____2541  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm)) in
                          trytac' uu____2532 in
                        bind uu____2525
                          (fun uu___57_2548  ->
                             match uu___57_2548 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2556 -> fail e))) in
        FStar_All.pipe_left (wrap_err "exact") uu____2490
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2571 =
             let uu____2578 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2578 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2571 in
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
          let uu____2638 = f x in
          bind uu____2638
            (fun y  ->
               let uu____2646 = mapM f xs in
               bind uu____2646 (fun ys  -> ret (y :: ys)))
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2664 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2681 =
               let uu____2686 = t_exact false true tm in trytac uu____2686 in
             bind uu____2681
               (fun uu___59_2693  ->
                  match uu___59_2693 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2699 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2699 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2731  ->
                                let uu____2732 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2732)
                             (fun uu____2735  ->
                                let uu____2736 =
                                  let uu____2737 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2737 in
                                if uu____2736
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2741 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2741
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2761 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2761 in
                                        let uu____2762 =
                                          __apply uopt tm' typ' in
                                        bind uu____2762
                                          (fun uu____2770  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2772 =
                                               let uu____2773 =
                                                 let uu____2776 =
                                                   let uu____2777 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2777 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2776 in
                                               uu____2773.FStar_Syntax_Syntax.n in
                                             match uu____2772 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2805) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2833 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2833
                                                      then ret ()
                                                      else
                                                        (let uu____2837 =
                                                           let uu____2840 =
                                                             let uu___85_2841
                                                               = goal in
                                                             let uu____2842 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2843 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___85_2841.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2842;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2843;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___85_2841.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2840] in
                                                         add_goals uu____2837))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2889 =
        mlog
          (fun uu____2894  ->
             let uu____2895 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2895)
          (fun uu____2897  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2901 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2901
                    (fun uu____2922  ->
                       match uu____2922 with
                       | (tm1,typ,guard) ->
                           let uu____2934 =
                             let uu____2937 =
                               let uu____2940 = __apply uopt tm1 typ in
                               bind uu____2940
                                 (fun uu____2944  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2937 in
                           let uu____2945 =
                             let uu____2948 =
                               tts goal.FStar_Tactics_Types.context tm1 in
                             let uu____2949 =
                               tts goal.FStar_Tactics_Types.context typ in
                             let uu____2950 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2948 uu____2949 uu____2950 in
                           try_unif uu____2934 uu____2945))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2889
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2962 =
      let uu____2965 =
        mlog
          (fun uu____2970  ->
             let uu____2971 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2971)
          (fun uu____2974  ->
             let is_unit_t t =
               let uu____2979 =
                 let uu____2980 = FStar_Syntax_Subst.compress t in
                 uu____2980.FStar_Syntax_Syntax.n in
               match uu____2979 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____2984 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____2988 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2988
                    (fun uu____3010  ->
                       match uu____3010 with
                       | (tm1,t,guard) ->
                           let uu____3022 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____3022 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3052 =
                                     FStar_List.fold_left
                                       (fun uu____3098  ->
                                          fun uu____3099  ->
                                            match (uu____3098, uu____3099)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____3202 =
                                                  is_unit_t b_t in
                                                if uu____3202
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3240 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____3240 with
                                                   | (u,uu____3270,g_u) ->
                                                       let uu____3284 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____3284,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____3052 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3354 =
                                         let uu____3363 =
                                           let uu____3372 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3372.FStar_Syntax_Syntax.effect_args in
                                         match uu____3363 with
                                         | pre::post::uu____3383 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3424 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3354 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3456 =
                                                let uu____3465 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3465] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3456 in
                                            let uu____3466 =
                                              let uu____3467 =
                                                let uu____3468 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3468
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3467 in
                                            if uu____3466
                                            then
                                              let uu____3471 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3472 =
                                                let uu____3473 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1 in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3473 in
                                              let uu____3474 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3471 uu____3472
                                                uu____3474
                                            else
                                              (let uu____3476 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3476
                                                 (fun uu____3481  ->
                                                    let uu____3482 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit in
                                                    bind uu____3482
                                                      (fun uu____3490  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3501 =
                                                               let uu____3508
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3508 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3501 in
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
                                                           let uu____3549 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3549
                                                           with
                                                           | (hd1,uu____3565)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3587)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3612
                                                                    -> false) in
                                                         let uu____3613 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3685
                                                                    ->
                                                                   match uu____3685
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3713)
                                                                    ->
                                                                    let uu____3714
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____3714
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3740)
                                                                    ->
                                                                    let uu____3761
                                                                    =
                                                                    let uu____3762
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3762.FStar_Syntax_Syntax.n in
                                                                    (match uu____3761
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3775
                                                                    ->
                                                                    let uu____3792
                                                                    =
                                                                    let uu____3801
                                                                    =
                                                                    let uu____3804
                                                                    =
                                                                    let uu___88_3805
                                                                    = goal in
                                                                    let uu____3806
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3807
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___88_3805.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3806;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3807;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___88_3805.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___88_3805.FStar_Tactics_Types.is_guard)
                                                                    } in
                                                                    [uu____3804] in
                                                                    (uu____3801,
                                                                    []) in
                                                                    ret
                                                                    uu____3792
                                                                    | 
                                                                    uu____3820
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____3822
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    () in
                                                                    if
                                                                    uu____3822
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term in
                                                                    let uu____3825
                                                                    =
                                                                    let uu____3832
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3832
                                                                    term1 in
                                                                    match uu____3825
                                                                    with
                                                                    | 
                                                                    (uu____3833,uu____3834,g_typ)
                                                                    -> g_typ) in
                                                                    let uu____3836
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts in
                                                                    bind
                                                                    uu____3836
                                                                    (fun
                                                                    uu___60_3852
                                                                     ->
                                                                    match uu___60_3852
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
                                                         bind uu____3613
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3920
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3920 in
                                                              let smt_goals =
                                                                let uu____3942
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3942 in
                                                              let rec filter'
                                                                a f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____3997
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____3997
                                                                    then
                                                                    let uu____4000
                                                                    =
                                                                    filter'
                                                                    () f xs1 in
                                                                    x ::
                                                                    uu____4000
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
                                                                    let uu____4014
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____4014))
                                                                    a434 a435)
                                                                    (Obj.magic
                                                                    sub_goals)) in
                                                              let uu____4015
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts in
                                                              bind uu____4015
                                                                (fun
                                                                   uu____4020
                                                                    ->
                                                                   let uu____4021
                                                                    =
                                                                    let uu____4024
                                                                    =
                                                                    let uu____4025
                                                                    =
                                                                    let uu____4026
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4026 in
                                                                    Prims.op_Negation
                                                                    uu____4025 in
                                                                    if
                                                                    uu____4024
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret () in
                                                                   bind
                                                                    uu____4021
                                                                    (fun
                                                                    uu____4032
                                                                     ->
                                                                    let uu____4033
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals in
                                                                    bind
                                                                    uu____4033
                                                                    (fun
                                                                    uu____4037
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))) in
      focus uu____2965 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2962
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4057 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____4057 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4067::(e1,uu____4069)::(e2,uu____4071)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4130 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4152 = destruct_eq' typ in
    match uu____4152 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4182 = FStar_Syntax_Util.un_squash typ in
        (match uu____4182 with
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
        let uu____4238 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____4238 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4286 = aux e' in
               FStar_Util.map_opt uu____4286
                 (fun uu____4310  ->
                    match uu____4310 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____4331 = aux e in
      FStar_Util.map_opt uu____4331
        (fun uu____4355  ->
           match uu____4355 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____4410 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____4410
            (fun uu____4434  ->
               match uu____4434 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___89_4451 = bv in
                     let uu____4452 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___89_4451.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___89_4451.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4452
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___90_4461 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___90_4461.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___90_4461.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4474 = h in
         match uu____4474 with
         | (bv,uu____4478) ->
             mlog
               (fun uu____4482  ->
                  let uu____4483 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4484 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4483
                    uu____4484)
               (fun uu____4487  ->
                  let uu____4488 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4488 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4517 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4517 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4532 =
                             let uu____4533 = FStar_Syntax_Subst.compress x in
                             uu____4533.FStar_Syntax_Syntax.n in
                           (match uu____4532 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___91_4546 = bv1 in
                                  let uu____4547 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___91_4546.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___91_4546.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4547
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4553 =
                                  let uu___92_4554 = goal in
                                  let uu____4555 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4556 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4557 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4555;
                                    FStar_Tactics_Types.witness = uu____4556;
                                    FStar_Tactics_Types.goal_ty = uu____4557;
                                    FStar_Tactics_Types.opts =
                                      (uu___92_4554.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___92_4554.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4553
                            | uu____4558 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4559 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4584 = b in
           match uu____4584 with
           | (bv,uu____4588) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___93_4592 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___93_4592.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___93_4592.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4596 =
                   let uu____4597 =
                     let uu____4604 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4604) in
                   FStar_Syntax_Syntax.NT uu____4597 in
                 [uu____4596] in
               let uu____4605 = subst_goal bv bv' s1 goal in
               (match uu____4605 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4624 = b in
         match uu____4624 with
         | (bv,uu____4628) ->
             let uu____4629 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4629 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4658 = FStar_Syntax_Util.type_u () in
                  (match uu____4658 with
                   | (ty,u) ->
                       let uu____4667 = new_uvar "binder_retype" e0 ty in
                       bind uu____4667
                         (fun t'  ->
                            let bv'' =
                              let uu___94_4677 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___94_4677.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___94_4677.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4681 =
                                let uu____4682 =
                                  let uu____4689 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4689) in
                                FStar_Syntax_Syntax.NT uu____4682 in
                              [uu____4681] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___95_4697 = b1 in
                                   let uu____4698 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___95_4697.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___95_4697.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4698
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4704  ->
                                 let uu____4705 =
                                   let uu____4708 =
                                     let uu____4711 =
                                       let uu___96_4712 = goal in
                                       let uu____4713 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4714 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4713;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4714;
                                         FStar_Tactics_Types.opts =
                                           (uu___96_4712.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___96_4712.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4711] in
                                   add_goals uu____4708 in
                                 bind uu____4705
                                   (fun uu____4717  ->
                                      let uu____4718 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4718
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4739 = b in
           match uu____4739 with
           | (bv,uu____4743) ->
               let uu____4744 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4744 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4776 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4776 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___97_4781 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___97_4781.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___97_4781.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___98_4785 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___98_4785.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___98_4785.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___98_4785.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___98_4785.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4793 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4793 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4815 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4815 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___99_4849 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___99_4849.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___99_4849.FStar_Tactics_Types.is_guard)
              }))
let free_in: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool
  =
  fun bv  ->
    fun t  ->
      let uu____4856 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____4856
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____4872  ->
              let uu____4873 = FStar_Syntax_Print.binder_to_string b in
              let uu____4874 =
                let uu____4875 =
                  let uu____4876 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context in
                  FStar_All.pipe_right uu____4876 FStar_List.length in
                FStar_All.pipe_right uu____4875 FStar_Util.string_of_int in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____4873 uu____4874)
           (fun uu____4887  ->
              let uu____4888 = split_env bv goal.FStar_Tactics_Types.context in
              match uu____4888 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____4933 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort in
                        if uu____4933
                        then
                          let uu____4936 =
                            let uu____4937 =
                              FStar_Syntax_Print.bv_to_string bv' in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____4937 in
                          fail uu____4936
                        else check bvs2 in
                  let uu____4939 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty in
                  if uu____4939
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____4943 = check bvs in
                     bind uu____4943
                       (fun uu____4949  ->
                          let env' = push_bvs e' bvs in
                          let uu____4951 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty in
                          bind uu____4951
                            (fun ut  ->
                               let uu____4957 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut in
                               if uu____4957
                               then
                                 replace_cur
                                   (let uu___100_4962 = goal in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness = ut;
                                      FStar_Tactics_Types.goal_ty =
                                        (uu___100_4962.FStar_Tactics_Types.goal_ty);
                                      FStar_Tactics_Types.opts =
                                        (uu___100_4962.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___100_4962.FStar_Tactics_Types.is_guard)
                                    })
                               else
                                 fail
                                   "Cannot clear; binder appears in witness")))))
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4971 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4971 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____4985) ->
           let uu____4990 = FStar_Syntax_Syntax.mk_binder x in
           clear uu____4990)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___101_5006 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___101_5006.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___101_5006.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___101_5006.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___101_5006.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5008  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___102_5024 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___102_5024.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___102_5024.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___102_5024.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___102_5024.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5026  -> add_goals [g']))
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
            let uu____5058 = FStar_Syntax_Subst.compress t in
            uu____5058.FStar_Syntax_Syntax.n in
          let uu____5061 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___104_5067 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___104_5067.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___104_5067.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____5061
            (fun t1  ->
               let tn1 =
                 let uu____5075 =
                   let uu____5076 = FStar_Syntax_Subst.compress t1 in
                   uu____5076.FStar_Syntax_Syntax.n in
                 match uu____5075 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____5108 = ff hd1 in
                     bind uu____5108
                       (fun hd2  ->
                          let fa uu____5128 =
                            match uu____5128 with
                            | (a,q) ->
                                let uu____5141 = ff a in
                                bind uu____5141 (fun a1  -> ret (a1, q)) in
                          let uu____5154 = mapM fa args in
                          bind uu____5154
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5214 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____5214 with
                      | (bs1,t') ->
                          let uu____5223 =
                            let uu____5226 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____5226 t' in
                          bind uu____5223
                            (fun t''  ->
                               let uu____5230 =
                                 let uu____5231 =
                                   let uu____5248 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____5249 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____5248, uu____5249, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____5231 in
                               ret uu____5230))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5270 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___103_5277 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___103_5277.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___103_5277.FStar_Syntax_Syntax.vars)
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
            let uu____5306 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____5306 with
            | (t1,lcomp,g) ->
                let uu____5318 =
                  (let uu____5321 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____5321) ||
                    (let uu____5323 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____5323) in
                if uu____5318
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____5333 = new_uvar "pointwise_rec" env typ in
                     bind uu____5333
                       (fun ut  ->
                          log ps
                            (fun uu____5344  ->
                               let uu____5345 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____5346 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5345 uu____5346);
                          (let uu____5347 =
                             let uu____5350 =
                               let uu____5351 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____5351 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5350 opts in
                           bind uu____5347
                             (fun uu____5354  ->
                                let uu____5355 =
                                  bind tau
                                    (fun uu____5361  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____5367  ->
                                            let uu____5368 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____5369 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5368 uu____5369);
                                       ret ut1) in
                                focus uu____5355))) in
                   let uu____5370 = trytac' rewrite_eq in
                   bind uu____5370
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
           let uu____5412 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5412 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5449  ->
                     let uu____5450 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5450);
                bind dismiss_all
                  (fun uu____5453  ->
                     let uu____5454 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5454
                       (fun gt'  ->
                          log ps
                            (fun uu____5464  ->
                               let uu____5465 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5465);
                          (let uu____5466 = push_goals gs in
                           bind uu____5466
                             (fun uu____5470  ->
                                add_goals
                                  [(let uu___105_5472 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___105_5472.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___105_5472.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___105_5472.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___105_5472.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5494 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5494 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5506 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5506 with
            | (hd1,args) ->
                let uu____5539 =
                  let uu____5552 =
                    let uu____5553 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5553.FStar_Syntax_Syntax.n in
                  (uu____5552, args) in
                (match uu____5539 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5567::(l,uu____5569)::(r,uu____5571)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5618 =
                       let uu____5619 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5619 in
                     if uu____5618
                     then
                       let uu____5622 = tts g.FStar_Tactics_Types.context l in
                       let uu____5623 = tts g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5622 uu____5623
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5626) ->
                     let uu____5643 = tts g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5643))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5653 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5653
         (fun u  ->
            let g' =
              let uu___106_5660 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___106_5660.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___106_5660.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___106_5660.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___106_5660.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5663  ->
                 let uu____5664 =
                   let uu____5667 =
                     let uu____5668 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5668
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5667
                     g.FStar_Tactics_Types.opts in
                 bind uu____5664
                   (fun uu____5671  ->
                      let uu____5672 = add_goals [g'] in
                      bind uu____5672 (fun uu____5676  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___107_5695 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___107_5695.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___107_5695.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___107_5695.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___107_5695.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___107_5695.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___107_5695.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___107_5695.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___107_5695.FStar_Tactics_Types.entry_range)
              })
       | uu____5696 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___108_5713 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___108_5713.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___108_5713.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___108_5713.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___108_5713.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___108_5713.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___108_5713.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___108_5713.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___108_5713.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5722 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5740 =
      bind cur_goal
        (fun g  ->
           let uu____5754 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5754
             (fun uu____5790  ->
                match uu____5790 with
                | (t1,typ,guard) ->
                    let uu____5806 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5806 with
                     | (hd1,args) ->
                         let uu____5849 =
                           let uu____5862 =
                             let uu____5863 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5863.FStar_Syntax_Syntax.n in
                           (uu____5862, args) in
                         (match uu____5849 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5882)::(q,uu____5884)::[]) when
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
                                let uu___109_5922 = g in
                                let uu____5923 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5923;
                                  FStar_Tactics_Types.witness =
                                    (uu___109_5922.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___109_5922.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___109_5922.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___109_5922.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___110_5925 = g in
                                let uu____5926 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5926;
                                  FStar_Tactics_Types.witness =
                                    (uu___110_5925.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___110_5925.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___110_5925.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___110_5925.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5933  ->
                                   let uu____5934 = add_goals [g1; g2] in
                                   bind uu____5934
                                     (fun uu____5943  ->
                                        let uu____5944 =
                                          let uu____5949 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5950 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5949, uu____5950) in
                                        ret uu____5944))
                          | uu____5955 ->
                              let uu____5968 =
                                tts g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5968)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5740
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6006 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____6006);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___111_6013 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___111_6013.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___111_6013.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___111_6013.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___111_6013.FStar_Tactics_Types.is_guard)
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
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ty  ->
    fun tm  ->
      let uu____6057 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____6065 = __tc env tm in
             bind uu____6065
               (fun uu____6085  ->
                  match uu____6085 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____6057
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____6116 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6122 =
              let uu____6123 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6123 in
            new_uvar "uvar_env.2" env uu____6122 in
      bind uu____6116
        (fun typ  ->
           let uu____6135 = new_uvar "uvar_env" env typ in
           bind uu____6135 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____6147 =
      bind cur_goal
        (fun goal  ->
           let uu____6153 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____6153
             (fun uu____6173  ->
                match uu____6173 with
                | (t1,typ,guard) ->
                    let uu____6185 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____6185
                      (fun uu____6190  ->
                         let uu____6191 =
                           let uu____6194 =
                             let uu___112_6195 = goal in
                             let uu____6196 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____6197 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___112_6195.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6196;
                               FStar_Tactics_Types.goal_ty = uu____6197;
                               FStar_Tactics_Types.opts =
                                 (uu___112_6195.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____6194] in
                         add_goals uu____6191))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6147
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6215 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____6215)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6232  ->
             let uu____6233 = FStar_Options.unsafe_tactic_exec () in
             if uu____6233
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6239  -> fun uu____6240  -> false) in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
let goal_of_goal_ty:
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____6256 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____6256 with
      | (u,uu____6274,g_u) ->
          let g =
            let uu____6289 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6289;
              FStar_Tactics_Types.is_guard = false
            } in
          (g, g_u)
let proofstate_of_goal_ty:
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____6300 = goal_of_goal_ty env typ in
      match uu____6300 with
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