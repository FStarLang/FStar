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
          ((let uu____581 =
              let uu____584 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____584 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____581);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'Auu____671 . Prims.string -> 'Auu____671 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____682 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____682
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____687 . Prims.string -> Prims.string -> 'Auu____687 tac =
  fun msg  ->
    fun x  -> let uu____698 = FStar_Util.format1 msg x in fail uu____698
let fail2:
  'Auu____703 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____703 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____718 = FStar_Util.format2 msg x y in fail uu____718
let fail3:
  'Auu____724 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____724 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____743 = FStar_Util.format3 msg x y z in fail uu____743
let trytac': 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____773 = run t ps in
         match uu____773 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____794) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____819 = trytac' t in
    bind uu____819
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____846 -> ret FStar_Pervasives_Native.None)
let wrap_err: 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____872 = run t ps in
           match uu____872 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____889  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____902 =
          let uu____903 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck" in
          () in
        let debug_off uu____907 =
          let uu____908 = FStar_Options.set_options FStar_Options.Reset "" in
          () in
        (let uu____910 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346") in
         if uu____910
         then
           (debug_on ();
            (let uu____912 = FStar_Syntax_Print.term_to_string t1 in
             let uu____913 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____912
               uu____913))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2 in
           debug_off (); res
         with | uu____900_925 -> (debug_off (); false))
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____938 =
         let uu___290_939 = p in
         let uu____940 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___290_939.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___290_939.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___290_939.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____940;
           FStar_Tactics_Types.smt_goals =
             (uu___290_939.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___290_939.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___290_939.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___290_939.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___290_939.FStar_Tactics_Types.entry_range)
         } in
       set uu____938)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____953 = trysolve goal solution in
      if uu____953
      then dismiss
      else
        (let uu____957 =
           let uu____958 = tts goal.FStar_Tactics_Types.context solution in
           let uu____959 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____960 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____958 uu____959
             uu____960 in
         fail uu____957)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___291_967 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___291_967.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___291_967.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___291_967.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___291_967.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___291_967.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___291_967.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___291_967.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___291_967.FStar_Tactics_Types.entry_range)
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
      let uu____991 = FStar_TypeChecker_Env.pop_bv e in
      match uu____991 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____1009 =
      (let uu____1012 = aux b2 env in Prims.op_Negation uu____1012) &&
        (let uu____1014 = FStar_ST.op_Bang nwarn in
         uu____1014 < (Prims.parse_int "5")) in
    if uu____1009
    then
      ((let uu____1064 =
          let uu____1065 = goal_to_string g in
          FStar_Util.format1
            "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
            uu____1065 in
        FStar_Errors.warn
          (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____1064);
       (let uu____1066 =
          let uu____1067 = FStar_ST.op_Bang nwarn in
          uu____1067 + (Prims.parse_int "1") in
        FStar_ST.op_Colon_Equals nwarn uu____1066))
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___292_1182 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___292_1182.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___292_1182.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___292_1182.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___292_1182.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___292_1182.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___292_1182.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___292_1182.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___292_1182.FStar_Tactics_Types.entry_range)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___293_1200 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___293_1200.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___293_1200.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___293_1200.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___293_1200.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___293_1200.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___293_1200.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___293_1200.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___293_1200.FStar_Tactics_Types.entry_range)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___294_1218 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___294_1218.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___294_1218.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___294_1218.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___294_1218.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___294_1218.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___294_1218.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___294_1218.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___294_1218.FStar_Tactics_Types.entry_range)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___295_1236 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___295_1236.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___295_1236.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___295_1236.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___295_1236.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___295_1236.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___295_1236.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___295_1236.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___295_1236.FStar_Tactics_Types.entry_range)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1245  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___296_1257 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___296_1257.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___296_1257.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___296_1257.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___296_1257.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___296_1257.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___296_1257.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___296_1257.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___296_1257.FStar_Tactics_Types.entry_range)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1283 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1283 with
        | (u,uu____1299,g_u) ->
            let uu____1313 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1313 (fun uu____1317  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1321 = FStar_Syntax_Util.un_squash t in
    match uu____1321 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1331 =
          let uu____1332 = FStar_Syntax_Subst.compress t' in
          uu____1332.FStar_Syntax_Syntax.n in
        (match uu____1331 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1336 -> false)
    | uu____1337 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1345 = FStar_Syntax_Util.un_squash t in
    match uu____1345 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1355 =
          let uu____1356 = FStar_Syntax_Subst.compress t' in
          uu____1356.FStar_Syntax_Syntax.n in
        (match uu____1355 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1360 -> false)
    | uu____1361 -> false
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
            let uu____1399 = env.FStar_TypeChecker_Env.universe_of env phi in
            FStar_Syntax_Util.mk_squash uu____1399 phi in
          let uu____1400 = new_uvar reason env typ in
          bind uu____1400
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
             let uu____1456 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1456
           with | e1 -> fail "not typeable")
let must_trivial: env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1504 =
          let uu____1505 =
            let uu____1506 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1506 in
          Prims.op_Negation uu____1505 in
        if uu____1504 then fail "got non-trivial guard" else ret ()
      with | uu____1515 -> fail "got non-trivial guard"
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1523 =
      bind cur_goal
        (fun goal  ->
           let uu____1529 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1529
             (fun uu____1549  ->
                match uu____1549 with
                | (t1,typ,guard) ->
                    let uu____1561 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____1561 (fun uu____1565  -> ret typ))) in
    FStar_All.pipe_left (wrap_err "tc") uu____1523
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1586 = mk_irrelevant_goal reason env phi opts in
          bind uu____1586 (fun goal  -> add_goals [goal])
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
       let uu____1606 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1606
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1610 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1610))
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
          let uu____1627 =
            let uu____1628 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1628.FStar_TypeChecker_Env.guard_f in
          match uu____1627 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1632 = istrivial e f in
              if uu____1632
              then ret ()
              else
                (let uu____1636 = mk_irrelevant_goal reason e f opts in
                 bind uu____1636
                   (fun goal  ->
                      let goal1 =
                        let uu___301_1643 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___301_1643.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___301_1643.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___301_1643.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___301_1643.FStar_Tactics_Types.opts);
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
          let uu____1664 =
            let uu____1665 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1665.FStar_TypeChecker_Env.guard_f in
          match uu____1664 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1673 = istrivial e f in
              if uu____1673
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1681 = mk_irrelevant_goal reason e f opts in
                 bind uu____1681
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___302_1691 = goal in
                            {
                              FStar_Tactics_Types.context =
                                (uu___302_1691.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___302_1691.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___302_1691.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___302_1691.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1697 = is_irrelevant g in
       if uu____1697
       then bind dismiss (fun uu____1701  -> add_smt_goals [g])
       else
         (let uu____1703 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1703))
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
             let uu____1744 =
               try
                 let uu____1778 =
                   let uu____1787 = FStar_BigInt.to_int_fs n1 in
                   FStar_List.splitAt uu____1787 p.FStar_Tactics_Types.goals in
                 ret uu____1778
               with | uu____1809 -> fail "divide: not enough goals" in
             bind uu____1744
               (fun uu____1836  ->
                  match uu____1836 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___303_1862 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___303_1862.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___303_1862.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___303_1862.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___303_1862.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___303_1862.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___303_1862.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___303_1862.FStar_Tactics_Types.entry_range)
                        } in
                      let rp =
                        let uu___304_1864 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___304_1864.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___304_1864.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___304_1864.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___304_1864.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___304_1864.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___304_1864.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___304_1864.FStar_Tactics_Types.entry_range)
                        } in
                      let uu____1865 = set lp in
                      bind uu____1865
                        (fun uu____1873  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1887 = set rp in
                                     bind uu____1887
                                       (fun uu____1895  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___305_1911 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___305_1911.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___305_1911.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___305_1911.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___305_1911.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___305_1911.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___305_1911.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___305_1911.FStar_Tactics_Types.entry_range)
                                                      } in
                                                    let uu____1912 = set p' in
                                                    bind uu____1912
                                                      (fun uu____1920  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1938 = divide FStar_BigInt.one f idtac in
    bind uu____1938
      (fun uu____1951  -> match uu____1951 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1985::uu____1986 ->
             let uu____1989 =
               let uu____1998 = map tau in
               divide FStar_BigInt.one tau uu____1998 in
             bind uu____1989
               (fun uu____2016  ->
                  match uu____2016 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____2053 =
        bind t1
          (fun uu____2058  ->
             let uu____2059 = map t2 in
             bind uu____2059 (fun uu____2067  -> ret ())) in
      focus uu____2053
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____2078 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____2078 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2093 =
             let uu____2094 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____2094 in
           if uu____2093
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____2100 = new_uvar "intro" env' typ' in
              bind uu____2100
                (fun u  ->
                   let uu____2107 =
                     let uu____2108 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____2108 in
                   if uu____2107
                   then
                     let uu____2111 =
                       let uu____2114 =
                         let uu___308_2115 = goal in
                         let uu____2116 = bnorm env' u in
                         let uu____2117 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2116;
                           FStar_Tactics_Types.goal_ty = uu____2117;
                           FStar_Tactics_Types.opts =
                             (uu___308_2115.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___308_2115.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____2114 in
                     bind uu____2111 (fun uu____2119  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2125 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____2125)
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
       (let uu____2146 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____2146 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2165 =
              let uu____2166 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____2166 in
            if uu____2165
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____2182 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____2182; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____2184 =
                 let uu____2187 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____2187 in
               bind uu____2184
                 (fun u  ->
                    let lb =
                      let uu____2203 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2203 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2207 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2207 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2244 =
                            let uu____2247 =
                              let uu___309_2248 = goal in
                              let uu____2249 = bnorm env' u in
                              let uu____2250 =
                                let uu____2251 = comp_to_typ c in
                                bnorm env' uu____2251 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2249;
                                FStar_Tactics_Types.goal_ty = uu____2250;
                                FStar_Tactics_Types.opts =
                                  (uu___309_2248.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___309_2248.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2247 in
                          bind uu____2244
                            (fun uu____2258  ->
                               let uu____2259 =
                                 let uu____2264 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2264, b) in
                               ret uu____2259)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2278 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2278))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2302 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2302 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___310_2309 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___310_2309.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___310_2309.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___310_2309.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2327 =
          bind get
            (fun ps  ->
               let uu____2333 = __tc e t in
               bind uu____2333
                 (fun uu____2355  ->
                    match uu____2355 with
                    | (t1,uu____2365,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2371 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2371 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2327
let refine_intro: Prims.unit tac =
  let uu____2381 =
    bind cur_goal
      (fun g  ->
         let uu____2388 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
         match uu____2388 with
         | (uu____2401,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___311_2426 = g in
               {
                 FStar_Tactics_Types.context =
                   (uu___311_2426.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___311_2426.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___311_2426.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___311_2426.FStar_Tactics_Types.is_guard)
               } in
             let uu____2427 =
               let uu____2432 =
                 let uu____2437 =
                   let uu____2438 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2438] in
                 FStar_Syntax_Subst.open_term uu____2437 phi in
               match uu____2432 with
               | (bvs,phi1) ->
                   let uu____2445 =
                     let uu____2446 = FStar_List.hd bvs in
                     FStar_Pervasives_Native.fst uu____2446 in
                   (uu____2445, phi1) in
             (match uu____2427 with
              | (bv1,phi1) ->
                  let uu____2459 =
                    let uu____2462 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1 in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2462
                      g.FStar_Tactics_Types.opts in
                  bind uu____2459
                    (fun g2  ->
                       bind dismiss (fun uu____2466  -> add_goals [g1; g2])))) in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2381
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
             let uu____2490 = __tc env t in
             bind uu____2490
               (fun uu____2510  ->
                  match uu____2510 with
                  | (t1,typ,guard) ->
                      let uu____2522 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts in
                      bind uu____2522
                        (fun uu____2529  ->
                           mlog
                             (fun uu____2533  ->
                                let uu____2534 =
                                  tts goal.FStar_Tactics_Types.context typ in
                                let uu____2535 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2534
                                  uu____2535)
                             (fun uu____2538  ->
                                let uu____2539 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty in
                                if uu____2539
                                then solve goal t1
                                else
                                  (let uu____2543 =
                                     tts goal.FStar_Tactics_Types.context t1 in
                                   let uu____2544 =
                                     tts goal.FStar_Tactics_Types.context typ in
                                   let uu____2545 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty in
                                   fail3
                                     "%s : %s does not exactly solve the goal %s"
                                     uu____2543 uu____2544 uu____2545)))))
let t_exact:
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2559 =
          mlog
            (fun uu____2564  ->
               let uu____2565 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "exact: tm = %s\n" uu____2565)
            (fun uu____2568  ->
               let uu____2569 =
                 let uu____2576 =
                   __exact_now set_expected_typ1 force_guard tm in
                 trytac' uu____2576 in
               bind uu____2569
                 (fun uu___285_2585  ->
                    match uu___285_2585 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2594 =
                          let uu____2601 =
                            let uu____2604 =
                              norm [FStar_Syntax_Embeddings.Delta] in
                            bind uu____2604
                              (fun uu____2608  ->
                                 bind refine_intro
                                   (fun uu____2610  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm)) in
                          trytac' uu____2601 in
                        bind uu____2594
                          (fun uu___284_2617  ->
                             match uu___284_2617 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2625 -> fail e))) in
        FStar_All.pipe_left (wrap_err "exact") uu____2559
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2640 =
             let uu____2647 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2647 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2640 in
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
          let uu____2707 = f x in
          bind uu____2707
            (fun y  ->
               let uu____2715 = mapM f xs in
               bind uu____2715 (fun ys  -> ret (y :: ys)))
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2733 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2750 =
               let uu____2755 = t_exact false true tm in trytac uu____2755 in
             bind uu____2750
               (fun uu___286_2762  ->
                  match uu___286_2762 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2768 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2768 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2800  ->
                                let uu____2801 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2801)
                             (fun uu____2804  ->
                                let uu____2805 =
                                  let uu____2806 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2806 in
                                if uu____2805
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2810 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2810
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2830 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2830 in
                                        let uu____2831 =
                                          __apply uopt tm' typ' in
                                        bind uu____2831
                                          (fun uu____2839  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2841 =
                                               let uu____2842 =
                                                 let uu____2845 =
                                                   let uu____2846 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2846 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2845 in
                                               uu____2842.FStar_Syntax_Syntax.n in
                                             match uu____2841 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2874) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2902 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2902
                                                      then ret ()
                                                      else
                                                        (let uu____2906 =
                                                           let uu____2909 =
                                                             let uu___312_2910
                                                               = goal in
                                                             let uu____2911 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2912 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___312_2910.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2911;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2912;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___312_2910.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2909] in
                                                         add_goals uu____2906))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2958 =
        mlog
          (fun uu____2963  ->
             let uu____2964 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2964)
          (fun uu____2966  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2970 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2970
                    (fun uu____2991  ->
                       match uu____2991 with
                       | (tm1,typ,guard) ->
                           let uu____3003 =
                             let uu____3006 =
                               let uu____3009 = __apply uopt tm1 typ in
                               bind uu____3009
                                 (fun uu____3013  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____3006 in
                           let uu____3014 =
                             let uu____3017 =
                               tts goal.FStar_Tactics_Types.context tm1 in
                             let uu____3018 =
                               tts goal.FStar_Tactics_Types.context typ in
                             let uu____3019 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3017 uu____3018 uu____3019 in
                           try_unif uu____3003 uu____3014))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2958
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____3031 =
      let uu____3034 =
        mlog
          (fun uu____3039  ->
             let uu____3040 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3040)
          (fun uu____3043  ->
             let is_unit_t t =
               let uu____3048 =
                 let uu____3049 = FStar_Syntax_Subst.compress t in
                 uu____3049.FStar_Syntax_Syntax.n in
               match uu____3048 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3053 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____3057 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____3057
                    (fun uu____3079  ->
                       match uu____3079 with
                       | (tm1,t,guard) ->
                           let uu____3091 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____3091 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3121 =
                                     FStar_List.fold_left
                                       (fun uu____3167  ->
                                          fun uu____3168  ->
                                            match (uu____3167, uu____3168)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____3271 =
                                                  is_unit_t b_t in
                                                if uu____3271
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3309 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____3309 with
                                                   | (u,uu____3339,g_u) ->
                                                       let uu____3353 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____3353,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____3121 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3423 =
                                         let uu____3432 =
                                           let uu____3441 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3441.FStar_Syntax_Syntax.effect_args in
                                         match uu____3432 with
                                         | pre::post::uu____3452 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3493 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3423 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3525 =
                                                let uu____3534 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3534] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3525 in
                                            let uu____3535 =
                                              let uu____3536 =
                                                let uu____3537 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3537
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3536 in
                                            if uu____3535
                                            then
                                              let uu____3540 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3541 =
                                                let uu____3542 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1 in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3542 in
                                              let uu____3543 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3540 uu____3541
                                                uu____3543
                                            else
                                              (let solution =
                                                 let uu____3546 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3546 in
                                               let uu____3547 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3547
                                                 (fun uu____3552  ->
                                                    let uu____3553 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit in
                                                    bind uu____3553
                                                      (fun uu____3561  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3572 =
                                                               let uu____3579
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3579 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3572 in
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
                                                           let uu____3620 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3620
                                                           with
                                                           | (hd1,uu____3636)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3658)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3683
                                                                    -> false) in
                                                         let uu____3684 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3756
                                                                    ->
                                                                   match uu____3756
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3784)
                                                                    ->
                                                                    let uu____3785
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____3785
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3811)
                                                                    ->
                                                                    let uu____3832
                                                                    =
                                                                    let uu____3833
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3833.FStar_Syntax_Syntax.n in
                                                                    (match uu____3832
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3846
                                                                    ->
                                                                    let uu____3863
                                                                    =
                                                                    let uu____3872
                                                                    =
                                                                    let uu____3875
                                                                    =
                                                                    let uu___315_3876
                                                                    = goal in
                                                                    let uu____3877
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3878
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___315_3876.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3877;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3878;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___315_3876.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___315_3876.FStar_Tactics_Types.is_guard)
                                                                    } in
                                                                    [uu____3875] in
                                                                    (uu____3872,
                                                                    []) in
                                                                    ret
                                                                    uu____3863
                                                                    | 
                                                                    uu____3891
                                                                    ->
                                                                    let term1
                                                                    =
                                                                    bnorm env
                                                                    term in
                                                                    let uu____3893
                                                                    =
                                                                    let uu____3900
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3900
                                                                    term1 in
                                                                    (match uu____3893
                                                                    with
                                                                    | 
                                                                    (uu____3911,uu____3912,g_typ)
                                                                    ->
                                                                    let uu____3914
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts in
                                                                    bind
                                                                    uu____3914
                                                                    (fun
                                                                    uu___287_3930
                                                                     ->
                                                                    match uu___287_3930
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
                                                         bind uu____3684
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3998
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3998 in
                                                              let smt_goals =
                                                                let uu____4020
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____4020 in
                                                              let rec filter'
                                                                f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4076
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____4076
                                                                    then
                                                                    let uu____4079
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____4079
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                              let sub_goals1
                                                                =
                                                                filter'
                                                                  (fun g  ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4093
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____4093)
                                                                  sub_goals in
                                                              let uu____4094
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts in
                                                              bind uu____4094
                                                                (fun
                                                                   uu____4099
                                                                    ->
                                                                   let uu____4100
                                                                    =
                                                                    let uu____4103
                                                                    =
                                                                    let uu____4104
                                                                    =
                                                                    let uu____4105
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4105 in
                                                                    Prims.op_Negation
                                                                    uu____4104 in
                                                                    if
                                                                    uu____4103
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret () in
                                                                   bind
                                                                    uu____4100
                                                                    (fun
                                                                    uu____4111
                                                                     ->
                                                                    let uu____4112
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals in
                                                                    bind
                                                                    uu____4112
                                                                    (fun
                                                                    uu____4116
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))) in
      focus uu____3034 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3031
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4136 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____4136 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4146::(e1,uu____4148)::(e2,uu____4150)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4209 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4231 = destruct_eq' typ in
    match uu____4231 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4261 = FStar_Syntax_Util.un_squash typ in
        (match uu____4261 with
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
        let uu____4317 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____4317 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4365 = aux e' in
               FStar_Util.map_opt uu____4365
                 (fun uu____4389  ->
                    match uu____4389 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____4410 = aux e in
      FStar_Util.map_opt uu____4410
        (fun uu____4434  ->
           match uu____4434 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____4489 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____4489
            (fun uu____4513  ->
               match uu____4513 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___316_4530 = bv in
                     let uu____4531 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___316_4530.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___316_4530.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4531
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___317_4540 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___317_4540.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___317_4540.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4553 = h in
         match uu____4553 with
         | (bv,uu____4557) ->
             mlog
               (fun uu____4561  ->
                  let uu____4562 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4563 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4562
                    uu____4563)
               (fun uu____4566  ->
                  let uu____4567 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4567 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4596 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4596 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4611 =
                             let uu____4612 = FStar_Syntax_Subst.compress x in
                             uu____4612.FStar_Syntax_Syntax.n in
                           (match uu____4611 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___318_4625 = bv1 in
                                  let uu____4626 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___318_4625.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___318_4625.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4626
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4632 =
                                  let uu___319_4633 = goal in
                                  let uu____4634 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4635 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4636 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4634;
                                    FStar_Tactics_Types.witness = uu____4635;
                                    FStar_Tactics_Types.goal_ty = uu____4636;
                                    FStar_Tactics_Types.opts =
                                      (uu___319_4633.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___319_4633.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4632
                            | uu____4637 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4638 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4663 = b in
           match uu____4663 with
           | (bv,uu____4667) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___320_4671 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___320_4671.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___320_4671.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4675 =
                   let uu____4676 =
                     let uu____4683 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4683) in
                   FStar_Syntax_Syntax.NT uu____4676 in
                 [uu____4675] in
               let uu____4684 = subst_goal bv bv' s1 goal in
               (match uu____4684 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4703 = b in
         match uu____4703 with
         | (bv,uu____4707) ->
             let uu____4708 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4708 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4737 = FStar_Syntax_Util.type_u () in
                  (match uu____4737 with
                   | (ty,u) ->
                       let uu____4746 = new_uvar "binder_retype" e0 ty in
                       bind uu____4746
                         (fun t'  ->
                            let bv'' =
                              let uu___321_4756 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___321_4756.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___321_4756.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4760 =
                                let uu____4761 =
                                  let uu____4768 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4768) in
                                FStar_Syntax_Syntax.NT uu____4761 in
                              [uu____4760] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___322_4776 = b1 in
                                   let uu____4777 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___322_4776.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___322_4776.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4777
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4783  ->
                                 let uu____4784 =
                                   let uu____4787 =
                                     let uu____4790 =
                                       let uu___323_4791 = goal in
                                       let uu____4792 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4793 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4792;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4793;
                                         FStar_Tactics_Types.opts =
                                           (uu___323_4791.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___323_4791.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4790] in
                                   add_goals uu____4787 in
                                 bind uu____4784
                                   (fun uu____4796  ->
                                      let uu____4797 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4797
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4818 = b in
           match uu____4818 with
           | (bv,uu____4822) ->
               let uu____4823 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4823 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4855 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4855 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___324_4860 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___324_4860.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___324_4860.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___325_4864 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___325_4864.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___325_4864.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___325_4864.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___325_4864.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4870 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4870 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4892 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4892 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___326_4926 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___326_4926.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___326_4926.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4937 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4937 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4958 = FStar_Syntax_Print.bv_to_string x in
               let uu____4959 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4958 uu____4959
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4966 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4966 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4988 = FStar_Util.set_mem x fns_ty in
           if uu____4988
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4992 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4992
                (fun u  ->
                   let uu____4998 =
                     let uu____4999 = trysolve goal u in
                     Prims.op_Negation uu____4999 in
                   if uu____4998
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___327_5004 = goal in
                        let uu____5005 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____5005;
                          FStar_Tactics_Types.goal_ty =
                            (uu___327_5004.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___327_5004.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___327_5004.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____5007  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____5018 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____5018 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____5042  ->
                    let uu____5043 = clear b in
                    bind uu____5043
                      (fun uu____5047  ->
                         bind intro (fun uu____5049  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___328_5065 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___328_5065.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___328_5065.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___328_5065.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___328_5065.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5067  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___329_5083 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___329_5083.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___329_5083.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___329_5083.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___329_5083.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5085  -> add_goals [g']))
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
            let uu____5117 = FStar_Syntax_Subst.compress t in
            uu____5117.FStar_Syntax_Syntax.n in
          let uu____5120 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___331_5126 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___331_5126.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___331_5126.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____5120
            (fun t1  ->
               let tn1 =
                 let uu____5134 =
                   let uu____5135 = FStar_Syntax_Subst.compress t1 in
                   uu____5135.FStar_Syntax_Syntax.n in
                 match uu____5134 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____5167 = ff hd1 in
                     bind uu____5167
                       (fun hd2  ->
                          let fa uu____5187 =
                            match uu____5187 with
                            | (a,q) ->
                                let uu____5200 = ff a in
                                bind uu____5200 (fun a1  -> ret (a1, q)) in
                          let uu____5213 = mapM fa args in
                          bind uu____5213
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5273 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____5273 with
                      | (bs1,t') ->
                          let uu____5282 =
                            let uu____5285 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____5285 t' in
                          bind uu____5282
                            (fun t''  ->
                               let uu____5289 =
                                 let uu____5290 =
                                   let uu____5307 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____5308 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____5307, uu____5308, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____5290 in
                               ret uu____5289))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5329 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___330_5336 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___330_5336.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___330_5336.FStar_Syntax_Syntax.vars)
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
            let uu____5365 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____5365 with
            | (t1,lcomp,g) ->
                let uu____5377 =
                  (let uu____5380 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____5380) ||
                    (let uu____5382 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____5382) in
                if uu____5377
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____5392 = new_uvar "pointwise_rec" env typ in
                     bind uu____5392
                       (fun ut  ->
                          log ps
                            (fun uu____5403  ->
                               let uu____5404 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____5405 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5404 uu____5405);
                          (let uu____5406 =
                             let uu____5409 =
                               let uu____5410 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____5410 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5409 opts in
                           bind uu____5406
                             (fun uu____5413  ->
                                let uu____5414 =
                                  bind tau
                                    (fun uu____5420  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____5426  ->
                                            let uu____5427 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____5428 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5427 uu____5428);
                                       ret ut1) in
                                focus uu____5414))) in
                   let uu____5429 = trytac' rewrite_eq in
                   bind uu____5429
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
           let uu____5471 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5471 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5508  ->
                     let uu____5509 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5509);
                bind dismiss_all
                  (fun uu____5512  ->
                     let uu____5513 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5513
                       (fun gt'  ->
                          log ps
                            (fun uu____5523  ->
                               let uu____5524 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5524);
                          (let uu____5525 = push_goals gs in
                           bind uu____5525
                             (fun uu____5529  ->
                                add_goals
                                  [(let uu___332_5531 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___332_5531.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___332_5531.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___332_5531.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___332_5531.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5551 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5551 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5563 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5563 with
            | (hd1,args) ->
                let uu____5596 =
                  let uu____5609 =
                    let uu____5610 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5610.FStar_Syntax_Syntax.n in
                  (uu____5609, args) in
                (match uu____5596 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5624::(l,uu____5626)::(r,uu____5628)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5675 =
                       let uu____5676 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5676 in
                     if uu____5675
                     then
                       let uu____5679 = tts g.FStar_Tactics_Types.context l in
                       let uu____5680 = tts g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5679 uu____5680
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5683) ->
                     let uu____5700 = tts g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5700))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5708 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5708
         (fun u  ->
            let g' =
              let uu___333_5715 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___333_5715.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___333_5715.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___333_5715.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___333_5715.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5718  ->
                 let uu____5719 =
                   let uu____5722 =
                     let uu____5723 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5723
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5722
                     g.FStar_Tactics_Types.opts in
                 bind uu____5719
                   (fun uu____5726  ->
                      let uu____5727 = add_goals [g'] in
                      bind uu____5727 (fun uu____5731  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___334_5748 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___334_5748.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___334_5748.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___334_5748.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___334_5748.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___334_5748.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___334_5748.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___334_5748.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___334_5748.FStar_Tactics_Types.entry_range)
              })
       | uu____5749 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___335_5764 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___335_5764.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___335_5764.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___335_5764.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___335_5764.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___335_5764.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___335_5764.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___335_5764.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___335_5764.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5771 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5789 =
      bind cur_goal
        (fun g  ->
           let uu____5803 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5803
             (fun uu____5839  ->
                match uu____5839 with
                | (t1,typ,guard) ->
                    let uu____5855 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5855 with
                     | (hd1,args) ->
                         let uu____5898 =
                           let uu____5911 =
                             let uu____5912 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5912.FStar_Syntax_Syntax.n in
                           (uu____5911, args) in
                         (match uu____5898 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5931)::(q,uu____5933)::[]) when
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
                                let uu___336_5971 = g in
                                let uu____5972 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5972;
                                  FStar_Tactics_Types.witness =
                                    (uu___336_5971.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___336_5971.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___336_5971.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___336_5971.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___337_5974 = g in
                                let uu____5975 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5975;
                                  FStar_Tactics_Types.witness =
                                    (uu___337_5974.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___337_5974.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___337_5974.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___337_5974.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5982  ->
                                   let uu____5983 = add_goals [g1; g2] in
                                   bind uu____5983
                                     (fun uu____5992  ->
                                        let uu____5993 =
                                          let uu____5998 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5999 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5998, uu____5999) in
                                        ret uu____5993))
                          | uu____6004 ->
                              let uu____6017 =
                                tts g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____6017)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5789
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6055 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____6055);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___338_6062 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___338_6062.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___338_6062.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___338_6062.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___338_6062.FStar_Tactics_Types.is_guard)
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
      let uu____6098 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____6106 = __tc env tm in
             bind uu____6106
               (fun uu____6126  ->
                  match uu____6126 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____6098
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____6157 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6163 =
              let uu____6164 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6164 in
            new_uvar "uvar_env.2" env uu____6163 in
      bind uu____6157
        (fun typ  ->
           let uu____6176 = new_uvar "uvar_env" env typ in
           bind uu____6176 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____6188 =
      bind cur_goal
        (fun goal  ->
           let uu____6194 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____6194
             (fun uu____6214  ->
                match uu____6214 with
                | (t1,typ,guard) ->
                    let uu____6226 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____6226
                      (fun uu____6231  ->
                         let uu____6232 =
                           let uu____6235 =
                             let uu___339_6236 = goal in
                             let uu____6237 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____6238 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___339_6236.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6237;
                               FStar_Tactics_Types.goal_ty = uu____6238;
                               FStar_Tactics_Types.opts =
                                 (uu___339_6236.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____6235] in
                         add_goals uu____6232))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6188
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6256 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____6256)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6273  ->
             let uu____6274 = FStar_Options.unsafe_tactic_exec () in
             if uu____6274
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6280  -> fun uu____6281  -> false) in
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
      let uu____6301 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____6301 with
      | (u,uu____6319,g_u) ->
          let g =
            let uu____6334 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6334;
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
      let uu____6349 = goal_of_goal_ty env typ in
      match uu____6349 with
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