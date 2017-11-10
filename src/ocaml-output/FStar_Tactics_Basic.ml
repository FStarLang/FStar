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
         let uu___368_913 = p in
         let uu____914 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___368_913.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___368_913.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___368_913.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____914;
           FStar_Tactics_Types.smt_goals =
             (uu___368_913.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___368_913.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___368_913.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___368_913.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___368_913.FStar_Tactics_Types.entry_range)
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
         (let uu___369_941 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___369_941.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___369_941.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___369_941.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___369_941.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___369_941.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___369_941.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___369_941.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___369_941.FStar_Tactics_Types.entry_range)
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
          (FStar_Errors.IllFormedGoal, uu____1041) in
        FStar_Errors.maybe_fatal_error
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
           (let uu___370_1155 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1155.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_1155.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_1155.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___370_1155.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_1155.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1155.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1155.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1155.FStar_Tactics_Types.entry_range)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___371_1173 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___371_1173.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___371_1173.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___371_1173.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___371_1173.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___371_1173.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___371_1173.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___371_1173.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___371_1173.FStar_Tactics_Types.entry_range)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___372_1191 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___372_1191.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___372_1191.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___372_1191.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___372_1191.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___372_1191.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___372_1191.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___372_1191.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___372_1191.FStar_Tactics_Types.entry_range)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___373_1209 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___373_1209.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___373_1209.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___373_1209.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___373_1209.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___373_1209.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___373_1209.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___373_1209.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___373_1209.FStar_Tactics_Types.entry_range)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1218  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___374_1230 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___374_1230.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___374_1230.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___374_1230.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___374_1230.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___374_1230.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___374_1230.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___374_1230.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___374_1230.FStar_Tactics_Types.entry_range)
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
                        let uu___379_1615 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___379_1615.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___379_1615.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___379_1615.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___379_1615.FStar_Tactics_Types.opts);
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
                           (let uu___380_1663 = goal in
                            {
                              FStar_Tactics_Types.context =
                                (uu___380_1663.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___380_1663.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___380_1663.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___380_1663.FStar_Tactics_Types.opts);
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
                        let uu___381_1834 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___381_1834.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___381_1834.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___381_1834.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___381_1834.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___381_1834.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___381_1834.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___381_1834.FStar_Tactics_Types.entry_range)
                        } in
                      let rp =
                        let uu___382_1836 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___382_1836.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___382_1836.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___382_1836.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___382_1836.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___382_1836.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___382_1836.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___382_1836.FStar_Tactics_Types.entry_range)
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
                                                      let uu___383_1883 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___383_1883.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___383_1883.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___383_1883.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___383_1883.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___383_1883.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___383_1883.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___383_1883.FStar_Tactics_Types.entry_range)
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
         | uu____1956::uu____1957 ->
             let uu____1960 =
               let uu____1969 = map tau in
               divide FStar_BigInt.one tau uu____1969 in
             bind uu____1960
               (fun uu____1987  ->
                  match uu____1987 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____2024 =
        bind t1
          (fun uu____2029  ->
             let uu____2030 = map t2 in
             bind uu____2030 (fun uu____2038  -> ret ())) in
      focus uu____2024
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____2049 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____2049 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2064 =
             let uu____2065 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____2065 in
           if uu____2064
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____2071 = new_uvar "intro" env' typ' in
              bind uu____2071
                (fun u  ->
                   let uu____2078 =
                     let uu____2079 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____2079 in
                   if uu____2078
                   then
                     let uu____2082 =
                       let uu____2085 =
                         let uu___386_2086 = goal in
                         let uu____2087 = bnorm env' u in
                         let uu____2088 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2087;
                           FStar_Tactics_Types.goal_ty = uu____2088;
                           FStar_Tactics_Types.opts =
                             (uu___386_2086.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___386_2086.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____2085 in
                     bind uu____2082 (fun uu____2090  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2096 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____2096)
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
       (let uu____2117 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____2117 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2136 =
              let uu____2137 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____2137 in
            if uu____2136
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____2153 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____2153; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____2155 =
                 let uu____2158 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____2158 in
               bind uu____2155
                 (fun u  ->
                    let lb =
                      let uu____2174 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2174 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2178 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2178 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2215 =
                            let uu____2218 =
                              let uu___387_2219 = goal in
                              let uu____2220 = bnorm env' u in
                              let uu____2221 =
                                let uu____2222 = comp_to_typ c in
                                bnorm env' uu____2222 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2220;
                                FStar_Tactics_Types.goal_ty = uu____2221;
                                FStar_Tactics_Types.opts =
                                  (uu___387_2219.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___387_2219.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2218 in
                          bind uu____2215
                            (fun uu____2229  ->
                               let uu____2230 =
                                 let uu____2235 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2235, b) in
                               ret uu____2230)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2249 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2249))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2273 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2273 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___388_2280 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___388_2280.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___388_2280.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___388_2280.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2298 =
          bind get
            (fun ps  ->
               let uu____2304 = __tc e t in
               bind uu____2304
                 (fun uu____2326  ->
                    match uu____2326 with
                    | (t1,uu____2336,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2342 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2342 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2298
let refine_intro: Prims.unit tac =
  let uu____2352 =
    bind cur_goal
      (fun g  ->
         let uu____2359 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
         match uu____2359 with
         | (uu____2372,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___389_2397 = g in
               {
                 FStar_Tactics_Types.context =
                   (uu___389_2397.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___389_2397.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___389_2397.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___389_2397.FStar_Tactics_Types.is_guard)
               } in
             let uu____2398 =
               let uu____2403 =
                 let uu____2408 =
                   let uu____2409 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2409] in
                 FStar_Syntax_Subst.open_term uu____2408 phi in
               match uu____2403 with
               | (bvs,phi1) ->
                   let uu____2416 =
                     let uu____2417 = FStar_List.hd bvs in
                     FStar_Pervasives_Native.fst uu____2417 in
                   (uu____2416, phi1) in
             (match uu____2398 with
              | (bv1,phi1) ->
                  let uu____2430 =
                    let uu____2433 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1 in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2433
                      g.FStar_Tactics_Types.opts in
                  bind uu____2430
                    (fun g2  ->
                       bind dismiss (fun uu____2437  -> add_goals [g1; g2])))) in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2352
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
             let uu____2461 = __tc env t in
             bind uu____2461
               (fun uu____2481  ->
                  match uu____2481 with
                  | (t1,typ,guard) ->
                      let uu____2493 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts in
                      bind uu____2493
                        (fun uu____2500  ->
                           mlog
                             (fun uu____2504  ->
                                let uu____2505 =
                                  tts goal.FStar_Tactics_Types.context typ in
                                let uu____2506 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2505
                                  uu____2506)
                             (fun uu____2509  ->
                                let uu____2510 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty in
                                if uu____2510
                                then solve goal t1
                                else
                                  (let uu____2514 =
                                     tts goal.FStar_Tactics_Types.context t1 in
                                   let uu____2515 =
                                     tts goal.FStar_Tactics_Types.context typ in
                                   let uu____2516 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty in
                                   fail3
                                     "%s : %s does not exactly solve the goal %s"
                                     uu____2514 uu____2515 uu____2516)))))
let t_exact:
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2530 =
          mlog
            (fun uu____2535  ->
               let uu____2536 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "exact: tm = %s\n" uu____2536)
            (fun uu____2539  ->
               let uu____2540 =
                 let uu____2547 =
                   __exact_now set_expected_typ1 force_guard tm in
                 trytac' uu____2547 in
               bind uu____2540
                 (fun uu___363_2556  ->
                    match uu___363_2556 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2565 =
                          let uu____2572 =
                            let uu____2575 =
                              norm [FStar_Syntax_Embeddings.Delta] in
                            bind uu____2575
                              (fun uu____2579  ->
                                 bind refine_intro
                                   (fun uu____2581  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm)) in
                          trytac' uu____2572 in
                        bind uu____2565
                          (fun uu___362_2588  ->
                             match uu___362_2588 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2596 -> fail e))) in
        FStar_All.pipe_left (wrap_err "exact") uu____2530
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2611 =
             let uu____2618 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2618 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2611 in
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
          let uu____2676 = f x in
          bind uu____2676
            (fun y  ->
               let uu____2684 = mapM f xs in
               bind uu____2684 (fun ys  -> ret (y :: ys)))
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2702 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2719 =
               let uu____2724 = t_exact false true tm in trytac uu____2724 in
             bind uu____2719
               (fun uu___364_2731  ->
                  match uu___364_2731 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2737 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2737 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2769  ->
                                let uu____2770 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2770)
                             (fun uu____2773  ->
                                let uu____2774 =
                                  let uu____2775 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2775 in
                                if uu____2774
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2779 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2779
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2799 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2799 in
                                        let uu____2800 =
                                          __apply uopt tm' typ' in
                                        bind uu____2800
                                          (fun uu____2808  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2810 =
                                               let uu____2811 =
                                                 let uu____2814 =
                                                   let uu____2815 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2815 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2814 in
                                               uu____2811.FStar_Syntax_Syntax.n in
                                             match uu____2810 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2843) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2871 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2871
                                                      then ret ()
                                                      else
                                                        (let uu____2875 =
                                                           let uu____2878 =
                                                             let uu___390_2879
                                                               = goal in
                                                             let uu____2880 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2881 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___390_2879.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2880;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2881;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___390_2879.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2878] in
                                                         add_goals uu____2875))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2927 =
        mlog
          (fun uu____2932  ->
             let uu____2933 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2933)
          (fun uu____2935  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2939 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2939
                    (fun uu____2960  ->
                       match uu____2960 with
                       | (tm1,typ,guard) ->
                           let uu____2972 =
                             let uu____2975 =
                               let uu____2978 = __apply uopt tm1 typ in
                               bind uu____2978
                                 (fun uu____2982  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2975 in
                           let uu____2983 =
                             let uu____2986 =
                               tts goal.FStar_Tactics_Types.context tm1 in
                             let uu____2987 =
                               tts goal.FStar_Tactics_Types.context typ in
                             let uu____2988 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2986 uu____2987 uu____2988 in
                           try_unif uu____2972 uu____2983))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2927
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____3000 =
      let uu____3003 =
        mlog
          (fun uu____3008  ->
             let uu____3009 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3009)
          (fun uu____3012  ->
             let is_unit_t t =
               let uu____3017 =
                 let uu____3018 = FStar_Syntax_Subst.compress t in
                 uu____3018.FStar_Syntax_Syntax.n in
               match uu____3017 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3022 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____3026 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____3026
                    (fun uu____3048  ->
                       match uu____3048 with
                       | (tm1,t,guard) ->
                           let uu____3060 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____3060 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3090 =
                                     FStar_List.fold_left
                                       (fun uu____3136  ->
                                          fun uu____3137  ->
                                            match (uu____3136, uu____3137)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____3240 =
                                                  is_unit_t b_t in
                                                if uu____3240
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3278 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____3278 with
                                                   | (u,uu____3308,g_u) ->
                                                       let uu____3322 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____3322,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____3090 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3392 =
                                         let uu____3401 =
                                           let uu____3410 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3410.FStar_Syntax_Syntax.effect_args in
                                         match uu____3401 with
                                         | pre::post::uu____3421 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3462 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3392 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3494 =
                                                let uu____3503 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3503] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3494 in
                                            let uu____3504 =
                                              let uu____3505 =
                                                let uu____3506 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3506
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3505 in
                                            if uu____3504
                                            then
                                              let uu____3509 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3510 =
                                                let uu____3511 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3511 in
                                              let uu____3512 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3509 uu____3510
                                                uu____3512
                                            else
                                              (let solution =
                                                 let uu____3515 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3515 in
                                               let uu____3516 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3516
                                                 (fun uu____3521  ->
                                                    let uu____3522 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit in
                                                    bind uu____3522
                                                      (fun uu____3530  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3541 =
                                                               let uu____3548
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3548 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3541 in
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
                                                           let uu____3589 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3589
                                                           with
                                                           | (hd1,uu____3605)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3627)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3652
                                                                    -> false) in
                                                         let uu____3653 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3725
                                                                    ->
                                                                   match uu____3725
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3753)
                                                                    ->
                                                                    let uu____3754
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____3754
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3780)
                                                                    ->
                                                                    let uu____3801
                                                                    =
                                                                    let uu____3802
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3802.FStar_Syntax_Syntax.n in
                                                                    (match uu____3801
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3815
                                                                    ->
                                                                    let uu____3832
                                                                    =
                                                                    let uu____3841
                                                                    =
                                                                    let uu____3844
                                                                    =
                                                                    let uu___393_3845
                                                                    = goal in
                                                                    let uu____3846
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3847
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___393_3845.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3846;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3847;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___393_3845.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___393_3845.FStar_Tactics_Types.is_guard)
                                                                    } in
                                                                    [uu____3844] in
                                                                    (uu____3841,
                                                                    []) in
                                                                    ret
                                                                    uu____3832
                                                                    | 
                                                                    uu____3860
                                                                    ->
                                                                    let term1
                                                                    =
                                                                    bnorm env
                                                                    term in
                                                                    let uu____3862
                                                                    =
                                                                    let uu____3869
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3869
                                                                    term1 in
                                                                    (match uu____3862
                                                                    with
                                                                    | 
                                                                    (uu____3880,uu____3881,g_typ)
                                                                    ->
                                                                    let uu____3883
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts in
                                                                    bind
                                                                    uu____3883
                                                                    (fun
                                                                    uu___365_3899
                                                                     ->
                                                                    match uu___365_3899
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
                                                         bind uu____3653
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3967
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3967 in
                                                              let smt_goals =
                                                                let uu____3989
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3989 in
                                                              let rec filter'
                                                                f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4045
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____4045
                                                                    then
                                                                    let uu____4048
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____4048
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                              let sub_goals1
                                                                =
                                                                filter'
                                                                  (fun g  ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4062
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____4062)
                                                                  sub_goals in
                                                              let uu____4063
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts in
                                                              bind uu____4063
                                                                (fun
                                                                   uu____4068
                                                                    ->
                                                                   let uu____4069
                                                                    =
                                                                    let uu____4072
                                                                    =
                                                                    let uu____4073
                                                                    =
                                                                    let uu____4074
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4074 in
                                                                    Prims.op_Negation
                                                                    uu____4073 in
                                                                    if
                                                                    uu____4072
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret () in
                                                                   bind
                                                                    uu____4069
                                                                    (fun
                                                                    uu____4080
                                                                     ->
                                                                    let uu____4081
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals in
                                                                    bind
                                                                    uu____4081
                                                                    (fun
                                                                    uu____4085
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))) in
      focus uu____3003 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3000
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4105 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____4105 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4115::(e1,uu____4117)::(e2,uu____4119)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4178 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4200 = destruct_eq' typ in
    match uu____4200 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4230 = FStar_Syntax_Util.un_squash typ in
        (match uu____4230 with
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
        let uu____4286 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____4286 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4334 = aux e' in
               FStar_Util.map_opt uu____4334
                 (fun uu____4358  ->
                    match uu____4358 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____4379 = aux e in
      FStar_Util.map_opt uu____4379
        (fun uu____4403  ->
           match uu____4403 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____4458 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____4458
            (fun uu____4482  ->
               match uu____4482 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___394_4499 = bv in
                     let uu____4500 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___394_4499.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___394_4499.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4500
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___395_4509 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___395_4509.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___395_4509.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4522 = h in
         match uu____4522 with
         | (bv,uu____4526) ->
             mlog
               (fun uu____4530  ->
                  let uu____4531 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4532 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4531
                    uu____4532)
               (fun uu____4535  ->
                  let uu____4536 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4536 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4565 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4565 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4580 =
                             let uu____4581 = FStar_Syntax_Subst.compress x in
                             uu____4581.FStar_Syntax_Syntax.n in
                           (match uu____4580 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___396_4594 = bv1 in
                                  let uu____4595 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___396_4594.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___396_4594.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4595
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4601 =
                                  let uu___397_4602 = goal in
                                  let uu____4603 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4604 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4605 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4603;
                                    FStar_Tactics_Types.witness = uu____4604;
                                    FStar_Tactics_Types.goal_ty = uu____4605;
                                    FStar_Tactics_Types.opts =
                                      (uu___397_4602.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___397_4602.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4601
                            | uu____4606 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4607 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4632 = b in
           match uu____4632 with
           | (bv,uu____4636) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___398_4640 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___398_4640.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___398_4640.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4644 =
                   let uu____4645 =
                     let uu____4652 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4652) in
                   FStar_Syntax_Syntax.NT uu____4645 in
                 [uu____4644] in
               let uu____4653 = subst_goal bv bv' s1 goal in
               (match uu____4653 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4672 = b in
         match uu____4672 with
         | (bv,uu____4676) ->
             let uu____4677 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4677 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4706 = FStar_Syntax_Util.type_u () in
                  (match uu____4706 with
                   | (ty,u) ->
                       let uu____4715 = new_uvar "binder_retype" e0 ty in
                       bind uu____4715
                         (fun t'  ->
                            let bv'' =
                              let uu___399_4725 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___399_4725.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___399_4725.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4729 =
                                let uu____4730 =
                                  let uu____4737 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4737) in
                                FStar_Syntax_Syntax.NT uu____4730 in
                              [uu____4729] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___400_4745 = b1 in
                                   let uu____4746 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___400_4745.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___400_4745.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4746
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4752  ->
                                 let uu____4753 =
                                   let uu____4756 =
                                     let uu____4759 =
                                       let uu___401_4760 = goal in
                                       let uu____4761 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4762 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4761;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4762;
                                         FStar_Tactics_Types.opts =
                                           (uu___401_4760.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___401_4760.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4759] in
                                   add_goals uu____4756 in
                                 bind uu____4753
                                   (fun uu____4765  ->
                                      let uu____4766 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4766
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4787 = b in
           match uu____4787 with
           | (bv,uu____4791) ->
               let uu____4792 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4792 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4824 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4824 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___402_4829 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___402_4829.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___402_4829.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___403_4833 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___403_4833.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___403_4833.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___403_4833.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___403_4833.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4839 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4839 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4861 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4861 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___404_4895 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___404_4895.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___404_4895.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4906 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4906 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4927 = FStar_Syntax_Print.bv_to_string x in
               let uu____4928 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4927 uu____4928
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4935 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4935 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4957 = FStar_Util.set_mem x fns_ty in
           if uu____4957
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4961 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4961
                (fun u  ->
                   let uu____4967 =
                     let uu____4968 = trysolve goal u in
                     Prims.op_Negation uu____4968 in
                   if uu____4967
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___405_4973 = goal in
                        let uu____4974 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4974;
                          FStar_Tactics_Types.goal_ty =
                            (uu___405_4973.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___405_4973.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___405_4973.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4976  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4987 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4987 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____5011  ->
                    let uu____5012 = clear b in
                    bind uu____5012
                      (fun uu____5016  ->
                         bind intro (fun uu____5018  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___406_5034 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___406_5034.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___406_5034.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___406_5034.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___406_5034.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5036  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___407_5052 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___407_5052.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___407_5052.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___407_5052.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___407_5052.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5054  -> add_goals [g']))
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
            let uu____5086 = FStar_Syntax_Subst.compress t in
            uu____5086.FStar_Syntax_Syntax.n in
          let uu____5089 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___409_5095 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___409_5095.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___409_5095.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____5089
            (fun t1  ->
               let tn1 =
                 let uu____5103 =
                   let uu____5104 = FStar_Syntax_Subst.compress t1 in
                   uu____5104.FStar_Syntax_Syntax.n in
                 match uu____5103 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____5136 = ff hd1 in
                     bind uu____5136
                       (fun hd2  ->
                          let fa uu____5156 =
                            match uu____5156 with
                            | (a,q) ->
                                let uu____5169 = ff a in
                                bind uu____5169 (fun a1  -> ret (a1, q)) in
                          let uu____5182 = mapM fa args in
                          bind uu____5182
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5242 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____5242 with
                      | (bs1,t') ->
                          let uu____5251 =
                            let uu____5254 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____5254 t' in
                          bind uu____5251
                            (fun t''  ->
                               let uu____5258 =
                                 let uu____5259 =
                                   let uu____5276 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____5277 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____5276, uu____5277, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____5259 in
                               ret uu____5258))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5298 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___408_5305 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___408_5305.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___408_5305.FStar_Syntax_Syntax.vars)
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
            let uu____5334 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____5334 with
            | (t1,lcomp,g) ->
                let uu____5346 =
                  (let uu____5349 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____5349) ||
                    (let uu____5351 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____5351) in
                if uu____5346
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____5361 = new_uvar "pointwise_rec" env typ in
                     bind uu____5361
                       (fun ut  ->
                          log ps
                            (fun uu____5372  ->
                               let uu____5373 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____5374 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5373 uu____5374);
                          (let uu____5375 =
                             let uu____5378 =
                               let uu____5379 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____5379 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5378 opts in
                           bind uu____5375
                             (fun uu____5382  ->
                                let uu____5383 =
                                  bind tau
                                    (fun uu____5389  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____5395  ->
                                            let uu____5396 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____5397 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5396 uu____5397);
                                       ret ut1) in
                                focus uu____5383))) in
                   let uu____5398 = trytac' rewrite_eq in
                   bind uu____5398
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
           let uu____5440 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5440 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5477  ->
                     let uu____5478 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5478);
                bind dismiss_all
                  (fun uu____5481  ->
                     let uu____5482 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5482
                       (fun gt'  ->
                          log ps
                            (fun uu____5492  ->
                               let uu____5493 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5493);
                          (let uu____5494 = push_goals gs in
                           bind uu____5494
                             (fun uu____5498  ->
                                add_goals
                                  [(let uu___410_5500 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___410_5500.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___410_5500.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___410_5500.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___410_5500.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5520 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5520 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5532 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5532 with
            | (hd1,args) ->
                let uu____5565 =
                  let uu____5578 =
                    let uu____5579 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5579.FStar_Syntax_Syntax.n in
                  (uu____5578, args) in
                (match uu____5565 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5593::(l,uu____5595)::(r,uu____5597)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5644 =
                       let uu____5645 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5645 in
                     if uu____5644
                     then
                       let uu____5648 = tts g.FStar_Tactics_Types.context l in
                       let uu____5649 = tts g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5648 uu____5649
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5652) ->
                     let uu____5669 = tts g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5669))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5677 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5677
         (fun u  ->
            let g' =
              let uu___411_5684 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___411_5684.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___411_5684.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___411_5684.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___411_5684.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5687  ->
                 let uu____5688 =
                   let uu____5691 =
                     let uu____5692 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5692
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5691
                     g.FStar_Tactics_Types.opts in
                 bind uu____5688
                   (fun uu____5695  ->
                      let uu____5696 = add_goals [g'] in
                      bind uu____5696 (fun uu____5700  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___412_5717 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___412_5717.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___412_5717.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___412_5717.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___412_5717.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___412_5717.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___412_5717.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___412_5717.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___412_5717.FStar_Tactics_Types.entry_range)
              })
       | uu____5718 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___413_5733 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___413_5733.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___413_5733.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___413_5733.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___413_5733.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___413_5733.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___413_5733.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___413_5733.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___413_5733.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5740 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5758 =
      bind cur_goal
        (fun g  ->
           let uu____5772 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5772
             (fun uu____5808  ->
                match uu____5808 with
                | (t1,typ,guard) ->
                    let uu____5824 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5824 with
                     | (hd1,args) ->
                         let uu____5867 =
                           let uu____5880 =
                             let uu____5881 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5881.FStar_Syntax_Syntax.n in
                           (uu____5880, args) in
                         (match uu____5867 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5900)::(q,uu____5902)::[]) when
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
                                let uu___414_5940 = g in
                                let uu____5941 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5941;
                                  FStar_Tactics_Types.witness =
                                    (uu___414_5940.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___414_5940.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___414_5940.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___414_5940.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___415_5943 = g in
                                let uu____5944 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5944;
                                  FStar_Tactics_Types.witness =
                                    (uu___415_5943.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___415_5943.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___415_5943.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___415_5943.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5951  ->
                                   let uu____5952 = add_goals [g1; g2] in
                                   bind uu____5952
                                     (fun uu____5961  ->
                                        let uu____5962 =
                                          let uu____5967 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5968 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5967, uu____5968) in
                                        ret uu____5962))
                          | uu____5973 ->
                              let uu____5986 =
                                tts g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5986)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5758
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6024 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____6024);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___416_6031 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___416_6031.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___416_6031.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___416_6031.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___416_6031.FStar_Tactics_Types.is_guard)
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
      let uu____6067 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____6075 = __tc env tm in
             bind uu____6075
               (fun uu____6095  ->
                  match uu____6095 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____6067
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____6126 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6132 =
              let uu____6133 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6133 in
            new_uvar "uvar_env.2" env uu____6132 in
      bind uu____6126
        (fun typ  ->
           let uu____6145 = new_uvar "uvar_env" env typ in
           bind uu____6145 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____6157 =
      bind cur_goal
        (fun goal  ->
           let uu____6163 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____6163
             (fun uu____6183  ->
                match uu____6183 with
                | (t1,typ,guard) ->
                    let uu____6195 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____6195
                      (fun uu____6200  ->
                         let uu____6201 =
                           let uu____6204 =
                             let uu___417_6205 = goal in
                             let uu____6206 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____6207 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___417_6205.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6206;
                               FStar_Tactics_Types.goal_ty = uu____6207;
                               FStar_Tactics_Types.opts =
                                 (uu___417_6205.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____6204] in
                         add_goals uu____6201))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6157
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6225 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____6225)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6242  ->
             let uu____6243 = FStar_Options.unsafe_tactic_exec () in
             if uu____6243
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6249  -> fun uu____6250  -> false) in
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
      let uu____6270 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____6270 with
      | (u,uu____6288,g_u) ->
          let g =
            let uu____6303 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6303;
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
      let uu____6318 = goal_of_goal_ty env typ in
      match uu____6318 with
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