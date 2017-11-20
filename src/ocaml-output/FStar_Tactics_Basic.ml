
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
         let uu___282_913 = p in
         let uu____914 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___282_913.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___282_913.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___282_913.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____914;
           FStar_Tactics_Types.smt_goals =
             (uu___282_913.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___282_913.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___282_913.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___282_913.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___282_913.FStar_Tactics_Types.entry_range)
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
         (let uu___283_941 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___283_941.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___283_941.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___283_941.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___283_941.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___283_941.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___283_941.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___283_941.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___283_941.FStar_Tactics_Types.entry_range)
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
          let uu____1037 = goal_to_string g in
          FStar_Util.format1
            "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
            uu____1037 in
        FStar_Errors.warn
          (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____1036);
       (let uu____1038 =
          let uu____1039 = FStar_ST.op_Bang nwarn in
          uu____1039 + (Prims.parse_int "1") in
        FStar_ST.op_Colon_Equals nwarn uu____1038))
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___284_1150 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___284_1150.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___284_1150.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___284_1150.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___284_1150.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___284_1150.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___284_1150.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___284_1150.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___284_1150.FStar_Tactics_Types.entry_range)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___285_1168 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___285_1168.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___285_1168.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___285_1168.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___285_1168.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___285_1168.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___285_1168.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___285_1168.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___285_1168.FStar_Tactics_Types.entry_range)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___286_1186 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___286_1186.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___286_1186.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___286_1186.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___286_1186.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___286_1186.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___286_1186.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___286_1186.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___286_1186.FStar_Tactics_Types.entry_range)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___287_1204 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___287_1204.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___287_1204.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___287_1204.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___287_1204.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___287_1204.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___287_1204.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___287_1204.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___287_1204.FStar_Tactics_Types.entry_range)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1213  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___288_1225 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___288_1225.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___288_1225.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___288_1225.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___288_1225.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___288_1225.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___288_1225.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___288_1225.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___288_1225.FStar_Tactics_Types.entry_range)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1251 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1251 with
        | (u,uu____1267,g_u) ->
            let uu____1281 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1281 (fun uu____1285  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1289 = FStar_Syntax_Util.un_squash t in
    match uu____1289 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1299 =
          let uu____1300 = FStar_Syntax_Subst.compress t' in
          uu____1300.FStar_Syntax_Syntax.n in
        (match uu____1299 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1304 -> false)
    | uu____1305 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1313 = FStar_Syntax_Util.un_squash t in
    match uu____1313 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1323 =
          let uu____1324 = FStar_Syntax_Subst.compress t' in
          uu____1324.FStar_Syntax_Syntax.n in
        (match uu____1323 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1328 -> false)
    | uu____1329 -> false
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
          let uu____1367 = new_uvar reason env typ in
          bind uu____1367
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
             let uu____1423 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1423
           with | e1 -> fail "not typeable")
let must_trivial: env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1471 =
          let uu____1472 =
            let uu____1473 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1473 in
          Prims.op_Negation uu____1472 in
        if uu____1471 then fail "got non-trivial guard" else ret ()
      with | uu____1482 -> fail "got non-trivial guard"
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1490 =
      bind cur_goal
        (fun goal  ->
           let uu____1496 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1496
             (fun uu____1516  ->
                match uu____1516 with
                | (t1,typ,guard) ->
                    let uu____1528 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____1528 (fun uu____1532  -> ret typ))) in
    FStar_All.pipe_left (wrap_err "tc") uu____1490
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1553 = mk_irrelevant_goal reason env phi opts in
          bind uu____1553 (fun goal  -> add_goals [goal])
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
       let uu____1573 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1573
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1577 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1577))
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
          let uu____1594 =
            let uu____1595 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1595.FStar_TypeChecker_Env.guard_f in
          match uu____1594 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1599 = istrivial e f in
              if uu____1599
              then ret ()
              else
                (let uu____1603 = mk_irrelevant_goal reason e f opts in
                 bind uu____1603
                   (fun goal  ->
                      let goal1 =
                        let uu___293_1610 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___293_1610.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___293_1610.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___293_1610.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___293_1610.FStar_Tactics_Types.opts);
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
          let uu____1631 =
            let uu____1632 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1632.FStar_TypeChecker_Env.guard_f in
          match uu____1631 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1640 = istrivial e f in
              if uu____1640
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1648 = mk_irrelevant_goal reason e f opts in
                 bind uu____1648
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___294_1658 = goal in
                            {
                              FStar_Tactics_Types.context =
                                (uu___294_1658.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___294_1658.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___294_1658.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___294_1658.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1664 = is_irrelevant g in
       if uu____1664
       then bind dismiss (fun uu____1668  -> add_smt_goals [g])
       else
         (let uu____1670 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1670))
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
             let uu____1711 =
               try
                 let uu____1745 =
                   let uu____1754 = FStar_BigInt.to_int_fs n1 in
                   FStar_List.splitAt uu____1754 p.FStar_Tactics_Types.goals in
                 ret uu____1745
               with | uu____1776 -> fail "divide: not enough goals" in
             bind uu____1711
               (fun uu____1803  ->
                  match uu____1803 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___295_1829 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___295_1829.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___295_1829.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___295_1829.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___295_1829.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___295_1829.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___295_1829.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___295_1829.FStar_Tactics_Types.entry_range)
                        } in
                      let rp =
                        let uu___296_1831 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___296_1831.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___296_1831.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___296_1831.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___296_1831.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___296_1831.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___296_1831.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___296_1831.FStar_Tactics_Types.entry_range)
                        } in
                      let uu____1832 = set lp in
                      bind uu____1832
                        (fun uu____1840  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1854 = set rp in
                                     bind uu____1854
                                       (fun uu____1862  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___297_1878 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___297_1878.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___297_1878.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___297_1878.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___297_1878.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___297_1878.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___297_1878.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___297_1878.FStar_Tactics_Types.entry_range)
                                                      } in
                                                    let uu____1879 = set p' in
                                                    bind uu____1879
                                                      (fun uu____1887  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1905 = divide FStar_BigInt.one f idtac in
    bind uu____1905
      (fun uu____1918  -> match uu____1918 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1952::uu____1953 ->
             let uu____1956 =
               let uu____1965 = map tau in
               divide FStar_BigInt.one tau uu____1965 in
             bind uu____1956
               (fun uu____1983  ->
                  match uu____1983 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____2020 =
        bind t1
          (fun uu____2025  ->
             let uu____2026 = map t2 in
             bind uu____2026 (fun uu____2034  -> ret ())) in
      focus uu____2020
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____2045 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____2045 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2060 =
             let uu____2061 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____2061 in
           if uu____2060
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____2067 = new_uvar "intro" env' typ' in
              bind uu____2067
                (fun u  ->
                   let uu____2074 =
                     let uu____2075 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____2075 in
                   if uu____2074
                   then
                     let uu____2078 =
                       let uu____2081 =
                         let uu___300_2082 = goal in
                         let uu____2083 = bnorm env' u in
                         let uu____2084 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2083;
                           FStar_Tactics_Types.goal_ty = uu____2084;
                           FStar_Tactics_Types.opts =
                             (uu___300_2082.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___300_2082.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____2081 in
                     bind uu____2078 (fun uu____2086  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2092 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____2092)
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
       (let uu____2113 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____2113 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2132 =
              let uu____2133 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____2133 in
            if uu____2132
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____2149 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____2149; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____2151 =
                 let uu____2154 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____2154 in
               bind uu____2151
                 (fun u  ->
                    let lb =
                      let uu____2170 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2170 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2174 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2174 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2211 =
                            let uu____2214 =
                              let uu___301_2215 = goal in
                              let uu____2216 = bnorm env' u in
                              let uu____2217 =
                                let uu____2218 = comp_to_typ c in
                                bnorm env' uu____2218 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2216;
                                FStar_Tactics_Types.goal_ty = uu____2217;
                                FStar_Tactics_Types.opts =
                                  (uu___301_2215.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___301_2215.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2214 in
                          bind uu____2211
                            (fun uu____2225  ->
                               let uu____2226 =
                                 let uu____2231 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2231, b) in
                               ret uu____2226)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2245 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2245))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2269 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2269 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___302_2276 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___302_2276.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___302_2276.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___302_2276.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2294 =
          bind get
            (fun ps  ->
               let uu____2300 = __tc e t in
               bind uu____2300
                 (fun uu____2322  ->
                    match uu____2322 with
                    | (t1,uu____2332,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2338 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2338 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2294
let refine_intro: Prims.unit tac =
  let uu____2348 =
    bind cur_goal
      (fun g  ->
         let uu____2355 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
         match uu____2355 with
         | (uu____2368,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___303_2393 = g in
               {
                 FStar_Tactics_Types.context =
                   (uu___303_2393.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___303_2393.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___303_2393.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___303_2393.FStar_Tactics_Types.is_guard)
               } in
             let uu____2394 =
               let uu____2399 =
                 let uu____2404 =
                   let uu____2405 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2405] in
                 FStar_Syntax_Subst.open_term uu____2404 phi in
               match uu____2399 with
               | (bvs,phi1) ->
                   let uu____2412 =
                     let uu____2413 = FStar_List.hd bvs in
                     FStar_Pervasives_Native.fst uu____2413 in
                   (uu____2412, phi1) in
             (match uu____2394 with
              | (bv1,phi1) ->
                  let uu____2426 =
                    let uu____2429 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1 in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2429
                      g.FStar_Tactics_Types.opts in
                  bind uu____2426
                    (fun g2  ->
                       bind dismiss (fun uu____2433  -> add_goals [g1; g2])))) in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2348
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
             let uu____2457 = __tc env t in
             bind uu____2457
               (fun uu____2477  ->
                  match uu____2477 with
                  | (t1,typ,guard) ->
                      let uu____2489 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts in
                      bind uu____2489
                        (fun uu____2496  ->
                           mlog
                             (fun uu____2500  ->
                                let uu____2501 =
                                  tts goal.FStar_Tactics_Types.context typ in
                                let uu____2502 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2501
                                  uu____2502)
                             (fun uu____2505  ->
                                let uu____2506 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty in
                                if uu____2506
                                then solve goal t1
                                else
                                  (let uu____2510 =
                                     tts goal.FStar_Tactics_Types.context t1 in
                                   let uu____2511 =
                                     tts goal.FStar_Tactics_Types.context typ in
                                   let uu____2512 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty in
                                   fail3
                                     "%s : %s does not exactly solve the goal %s"
                                     uu____2510 uu____2511 uu____2512)))))
let t_exact:
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2526 =
          mlog
            (fun uu____2531  ->
               let uu____2532 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "exact: tm = %s\n" uu____2532)
            (fun uu____2535  ->
               let uu____2536 =
                 let uu____2543 =
                   __exact_now set_expected_typ1 force_guard tm in
                 trytac' uu____2543 in
               bind uu____2536
                 (fun uu___277_2552  ->
                    match uu___277_2552 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2561 =
                          let uu____2568 =
                            let uu____2571 =
                              norm [FStar_Syntax_Embeddings.Delta] in
                            bind uu____2571
                              (fun uu____2575  ->
                                 bind refine_intro
                                   (fun uu____2577  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm)) in
                          trytac' uu____2568 in
                        bind uu____2561
                          (fun uu___276_2584  ->
                             match uu___276_2584 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2592 -> fail e))) in
        FStar_All.pipe_left (wrap_err "exact") uu____2526
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2607 =
             let uu____2614 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2614 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2607 in
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
          let uu____2674 = f x in
          bind uu____2674
            (fun y  ->
               let uu____2682 = mapM f xs in
               bind uu____2682 (fun ys  -> ret (y :: ys)))
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2700 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2717 =
               let uu____2722 = t_exact false true tm in trytac uu____2722 in
             bind uu____2717
               (fun uu___278_2729  ->
                  match uu___278_2729 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2735 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2735 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2767  ->
                                let uu____2768 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2768)
                             (fun uu____2771  ->
                                let uu____2772 =
                                  let uu____2773 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2773 in
                                if uu____2772
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2777 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2777
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2797 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2797 in
                                        let uu____2798 =
                                          __apply uopt tm' typ' in
                                        bind uu____2798
                                          (fun uu____2806  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2808 =
                                               let uu____2809 =
                                                 let uu____2812 =
                                                   let uu____2813 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2813 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2812 in
                                               uu____2809.FStar_Syntax_Syntax.n in
                                             match uu____2808 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2841) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2869 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2869
                                                      then ret ()
                                                      else
                                                        (let uu____2873 =
                                                           let uu____2876 =
                                                             let uu___304_2877
                                                               = goal in
                                                             let uu____2878 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2879 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___304_2877.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2878;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2879;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___304_2877.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2876] in
                                                         add_goals uu____2873))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2925 =
        mlog
          (fun uu____2930  ->
             let uu____2931 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2931)
          (fun uu____2933  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2937 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2937
                    (fun uu____2958  ->
                       match uu____2958 with
                       | (tm1,typ,guard) ->
                           let uu____2970 =
                             let uu____2973 =
                               let uu____2976 = __apply uopt tm1 typ in
                               bind uu____2976
                                 (fun uu____2980  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2973 in
                           let uu____2981 =
                             let uu____2984 =
                               tts goal.FStar_Tactics_Types.context tm1 in
                             let uu____2985 =
                               tts goal.FStar_Tactics_Types.context typ in
                             let uu____2986 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2984 uu____2985 uu____2986 in
                           try_unif uu____2970 uu____2981))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2925
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2998 =
      let uu____3001 =
        mlog
          (fun uu____3006  ->
             let uu____3007 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3007)
          (fun uu____3010  ->
             let is_unit_t t =
               let uu____3015 =
                 let uu____3016 = FStar_Syntax_Subst.compress t in
                 uu____3016.FStar_Syntax_Syntax.n in
               match uu____3015 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3020 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____3024 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____3024
                    (fun uu____3046  ->
                       match uu____3046 with
                       | (tm1,t,guard) ->
                           let uu____3058 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____3058 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3088 =
                                     FStar_List.fold_left
                                       (fun uu____3134  ->
                                          fun uu____3135  ->
                                            match (uu____3134, uu____3135)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____3238 =
                                                  is_unit_t b_t in
                                                if uu____3238
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3276 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____3276 with
                                                   | (u,uu____3306,g_u) ->
                                                       let uu____3320 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____3320,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____3088 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3390 =
                                         let uu____3399 =
                                           let uu____3408 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3408.FStar_Syntax_Syntax.effect_args in
                                         match uu____3399 with
                                         | pre::post::uu____3419 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3460 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3390 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3492 =
                                                let uu____3501 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3501] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3492 in
                                            let uu____3502 =
                                              let uu____3503 =
                                                let uu____3504 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3504
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3503 in
                                            if uu____3502
                                            then
                                              let uu____3507 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3508 =
                                                let uu____3509 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3509 in
                                              let uu____3510 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3507 uu____3508
                                                uu____3510
                                            else
                                              (let solution =
                                                 let uu____3513 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3513 in
                                               let uu____3514 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3514
                                                 (fun uu____3519  ->
                                                    let uu____3520 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit in
                                                    bind uu____3520
                                                      (fun uu____3528  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3539 =
                                                               let uu____3546
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3546 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3539 in
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
                                                           let uu____3587 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3587
                                                           with
                                                           | (hd1,uu____3603)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3625)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3650
                                                                    -> false) in
                                                         let uu____3651 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3723
                                                                    ->
                                                                   match uu____3723
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3751)
                                                                    ->
                                                                    let uu____3752
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____3752
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3778)
                                                                    ->
                                                                    let uu____3799
                                                                    =
                                                                    let uu____3800
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3800.FStar_Syntax_Syntax.n in
                                                                    (match uu____3799
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3813
                                                                    ->
                                                                    let uu____3830
                                                                    =
                                                                    let uu____3839
                                                                    =
                                                                    let uu____3842
                                                                    =
                                                                    let uu___307_3843
                                                                    = goal in
                                                                    let uu____3844
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3845
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___307_3843.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3844;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3845;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___307_3843.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___307_3843.FStar_Tactics_Types.is_guard)
                                                                    } in
                                                                    [uu____3842] in
                                                                    (uu____3839,
                                                                    []) in
                                                                    ret
                                                                    uu____3830
                                                                    | 
                                                                    uu____3858
                                                                    ->
                                                                    let term1
                                                                    =
                                                                    bnorm env
                                                                    term in
                                                                    let uu____3860
                                                                    =
                                                                    let uu____3867
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3867
                                                                    term1 in
                                                                    (match uu____3860
                                                                    with
                                                                    | 
                                                                    (uu____3878,uu____3879,g_typ)
                                                                    ->
                                                                    let uu____3881
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts in
                                                                    bind
                                                                    uu____3881
                                                                    (fun
                                                                    uu___279_3897
                                                                     ->
                                                                    match uu___279_3897
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
                                                         bind uu____3651
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3965
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3965 in
                                                              let smt_goals =
                                                                let uu____3987
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3987 in
                                                              let rec filter'
                                                                f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4043
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____4043
                                                                    then
                                                                    let uu____4046
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____4046
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                              let sub_goals1
                                                                =
                                                                filter'
                                                                  (fun g  ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4060
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____4060)
                                                                  sub_goals in
                                                              let uu____4061
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts in
                                                              bind uu____4061
                                                                (fun
                                                                   uu____4066
                                                                    ->
                                                                   let uu____4067
                                                                    =
                                                                    let uu____4070
                                                                    =
                                                                    let uu____4071
                                                                    =
                                                                    let uu____4072
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4072 in
                                                                    Prims.op_Negation
                                                                    uu____4071 in
                                                                    if
                                                                    uu____4070
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret () in
                                                                   bind
                                                                    uu____4067
                                                                    (fun
                                                                    uu____4078
                                                                     ->
                                                                    let uu____4079
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals in
                                                                    bind
                                                                    uu____4079
                                                                    (fun
                                                                    uu____4083
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))) in
      focus uu____3001 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2998
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4103 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____4103 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4113::(e1,uu____4115)::(e2,uu____4117)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4176 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4198 = destruct_eq' typ in
    match uu____4198 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4228 = FStar_Syntax_Util.un_squash typ in
        (match uu____4228 with
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
        let uu____4284 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____4284 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4332 = aux e' in
               FStar_Util.map_opt uu____4332
                 (fun uu____4356  ->
                    match uu____4356 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____4377 = aux e in
      FStar_Util.map_opt uu____4377
        (fun uu____4401  ->
           match uu____4401 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____4456 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____4456
            (fun uu____4480  ->
               match uu____4480 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___308_4497 = bv in
                     let uu____4498 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___308_4497.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___308_4497.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4498
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___309_4507 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___309_4507.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___309_4507.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4520 = h in
         match uu____4520 with
         | (bv,uu____4524) ->
             mlog
               (fun uu____4528  ->
                  let uu____4529 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4530 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4529
                    uu____4530)
               (fun uu____4533  ->
                  let uu____4534 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4534 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4563 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4563 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4578 =
                             let uu____4579 = FStar_Syntax_Subst.compress x in
                             uu____4579.FStar_Syntax_Syntax.n in
                           (match uu____4578 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___310_4592 = bv1 in
                                  let uu____4593 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___310_4592.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___310_4592.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4593
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4599 =
                                  let uu___311_4600 = goal in
                                  let uu____4601 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4602 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4603 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4601;
                                    FStar_Tactics_Types.witness = uu____4602;
                                    FStar_Tactics_Types.goal_ty = uu____4603;
                                    FStar_Tactics_Types.opts =
                                      (uu___311_4600.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___311_4600.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4599
                            | uu____4604 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4605 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4630 = b in
           match uu____4630 with
           | (bv,uu____4634) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___312_4638 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___312_4638.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___312_4638.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4642 =
                   let uu____4643 =
                     let uu____4650 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4650) in
                   FStar_Syntax_Syntax.NT uu____4643 in
                 [uu____4642] in
               let uu____4651 = subst_goal bv bv' s1 goal in
               (match uu____4651 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4670 = b in
         match uu____4670 with
         | (bv,uu____4674) ->
             let uu____4675 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4675 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4704 = FStar_Syntax_Util.type_u () in
                  (match uu____4704 with
                   | (ty,u) ->
                       let uu____4713 = new_uvar "binder_retype" e0 ty in
                       bind uu____4713
                         (fun t'  ->
                            let bv'' =
                              let uu___313_4723 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___313_4723.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___313_4723.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4727 =
                                let uu____4728 =
                                  let uu____4735 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4735) in
                                FStar_Syntax_Syntax.NT uu____4728 in
                              [uu____4727] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___314_4743 = b1 in
                                   let uu____4744 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___314_4743.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___314_4743.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4744
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4750  ->
                                 let uu____4751 =
                                   let uu____4754 =
                                     let uu____4757 =
                                       let uu___315_4758 = goal in
                                       let uu____4759 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4760 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4759;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4760;
                                         FStar_Tactics_Types.opts =
                                           (uu___315_4758.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___315_4758.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4757] in
                                   add_goals uu____4754 in
                                 bind uu____4751
                                   (fun uu____4763  ->
                                      let uu____4764 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4764
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4785 = b in
           match uu____4785 with
           | (bv,uu____4789) ->
               let uu____4790 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4790 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4822 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4822 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___316_4827 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___316_4827.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___316_4827.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___317_4831 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___317_4831.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___317_4831.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___317_4831.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___317_4831.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4837 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4837 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4859 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4859 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___318_4893 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___318_4893.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___318_4893.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4904 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4904 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4925 = FStar_Syntax_Print.bv_to_string x in
               let uu____4926 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4925 uu____4926
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4933 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4933 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4955 = FStar_Util.set_mem x fns_ty in
           if uu____4955
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4959 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4959
                (fun u  ->
                   let uu____4965 =
                     let uu____4966 = trysolve goal u in
                     Prims.op_Negation uu____4966 in
                   if uu____4965
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___319_4971 = goal in
                        let uu____4972 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4972;
                          FStar_Tactics_Types.goal_ty =
                            (uu___319_4971.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___319_4971.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___319_4971.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4974  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4985 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4985 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____5009  ->
                    let uu____5010 = clear b in
                    bind uu____5010
                      (fun uu____5014  ->
                         bind intro (fun uu____5016  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___320_5032 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___320_5032.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___320_5032.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___320_5032.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___320_5032.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5034  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___321_5050 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___321_5050.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___321_5050.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___321_5050.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___321_5050.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5052  -> add_goals [g']))
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
            let uu____5084 = FStar_Syntax_Subst.compress t in
            uu____5084.FStar_Syntax_Syntax.n in
          let uu____5087 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___323_5093 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___323_5093.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___323_5093.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____5087
            (fun t1  ->
               let tn1 =
                 let uu____5101 =
                   let uu____5102 = FStar_Syntax_Subst.compress t1 in
                   uu____5102.FStar_Syntax_Syntax.n in
                 match uu____5101 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____5134 = ff hd1 in
                     bind uu____5134
                       (fun hd2  ->
                          let fa uu____5154 =
                            match uu____5154 with
                            | (a,q) ->
                                let uu____5167 = ff a in
                                bind uu____5167 (fun a1  -> ret (a1, q)) in
                          let uu____5180 = mapM fa args in
                          bind uu____5180
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5240 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____5240 with
                      | (bs1,t') ->
                          let uu____5249 =
                            let uu____5252 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____5252 t' in
                          bind uu____5249
                            (fun t''  ->
                               let uu____5256 =
                                 let uu____5257 =
                                   let uu____5274 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____5275 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____5274, uu____5275, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____5257 in
                               ret uu____5256))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5296 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___322_5303 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___322_5303.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___322_5303.FStar_Syntax_Syntax.vars)
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
            let uu____5332 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____5332 with
            | (t1,lcomp,g) ->
                let uu____5344 =
                  (let uu____5347 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____5347) ||
                    (let uu____5349 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____5349) in
                if uu____5344
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____5359 = new_uvar "pointwise_rec" env typ in
                     bind uu____5359
                       (fun ut  ->
                          log ps
                            (fun uu____5370  ->
                               let uu____5371 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____5372 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5371 uu____5372);
                          (let uu____5373 =
                             let uu____5376 =
                               let uu____5377 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____5377 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5376 opts in
                           bind uu____5373
                             (fun uu____5380  ->
                                let uu____5381 =
                                  bind tau
                                    (fun uu____5387  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____5393  ->
                                            let uu____5394 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____5395 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5394 uu____5395);
                                       ret ut1) in
                                focus uu____5381))) in
                   let uu____5396 = trytac' rewrite_eq in
                   bind uu____5396
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
           let uu____5438 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5438 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5475  ->
                     let uu____5476 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5476);
                bind dismiss_all
                  (fun uu____5479  ->
                     let uu____5480 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5480
                       (fun gt'  ->
                          log ps
                            (fun uu____5490  ->
                               let uu____5491 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5491);
                          (let uu____5492 = push_goals gs in
                           bind uu____5492
                             (fun uu____5496  ->
                                add_goals
                                  [(let uu___324_5498 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___324_5498.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___324_5498.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___324_5498.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___324_5498.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5518 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5518 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5530 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5530 with
            | (hd1,args) ->
                let uu____5563 =
                  let uu____5576 =
                    let uu____5577 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5577.FStar_Syntax_Syntax.n in
                  (uu____5576, args) in
                (match uu____5563 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5591::(l,uu____5593)::(r,uu____5595)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5642 =
                       let uu____5643 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5643 in
                     if uu____5642
                     then
                       let uu____5646 = tts g.FStar_Tactics_Types.context l in
                       let uu____5647 = tts g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5646 uu____5647
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5650) ->
                     let uu____5667 = tts g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5667))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5675 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5675
         (fun u  ->
            let g' =
              let uu___325_5682 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___325_5682.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___325_5682.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___325_5682.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___325_5682.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5685  ->
                 let uu____5686 =
                   let uu____5689 =
                     let uu____5690 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5690
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5689
                     g.FStar_Tactics_Types.opts in
                 bind uu____5686
                   (fun uu____5693  ->
                      let uu____5694 = add_goals [g'] in
                      bind uu____5694 (fun uu____5698  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___326_5715 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___326_5715.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___326_5715.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___326_5715.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___326_5715.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___326_5715.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___326_5715.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___326_5715.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___326_5715.FStar_Tactics_Types.entry_range)
              })
       | uu____5716 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___327_5731 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___327_5731.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___327_5731.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___327_5731.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___327_5731.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___327_5731.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___327_5731.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___327_5731.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___327_5731.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5738 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5756 =
      bind cur_goal
        (fun g  ->
           let uu____5770 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5770
             (fun uu____5806  ->
                match uu____5806 with
                | (t1,typ,guard) ->
                    let uu____5822 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5822 with
                     | (hd1,args) ->
                         let uu____5865 =
                           let uu____5878 =
                             let uu____5879 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5879.FStar_Syntax_Syntax.n in
                           (uu____5878, args) in
                         (match uu____5865 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5898)::(q,uu____5900)::[]) when
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
                                let uu___328_5938 = g in
                                let uu____5939 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5939;
                                  FStar_Tactics_Types.witness =
                                    (uu___328_5938.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___328_5938.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___328_5938.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___328_5938.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___329_5941 = g in
                                let uu____5942 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5942;
                                  FStar_Tactics_Types.witness =
                                    (uu___329_5941.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___329_5941.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___329_5941.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___329_5941.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5949  ->
                                   let uu____5950 = add_goals [g1; g2] in
                                   bind uu____5950
                                     (fun uu____5959  ->
                                        let uu____5960 =
                                          let uu____5965 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5966 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5965, uu____5966) in
                                        ret uu____5960))
                          | uu____5971 ->
                              let uu____5984 =
                                tts g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5984)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5756
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6022 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____6022);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___330_6029 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___330_6029.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___330_6029.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___330_6029.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___330_6029.FStar_Tactics_Types.is_guard)
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
      let uu____6065 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____6073 = __tc env tm in
             bind uu____6073
               (fun uu____6093  ->
                  match uu____6093 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____6065
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____6124 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6130 =
              let uu____6131 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6131 in
            new_uvar "uvar_env.2" env uu____6130 in
      bind uu____6124
        (fun typ  ->
           let uu____6143 = new_uvar "uvar_env" env typ in
           bind uu____6143 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____6155 =
      bind cur_goal
        (fun goal  ->
           let uu____6161 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____6161
             (fun uu____6181  ->
                match uu____6181 with
                | (t1,typ,guard) ->
                    let uu____6193 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____6193
                      (fun uu____6198  ->
                         let uu____6199 =
                           let uu____6202 =
                             let uu___331_6203 = goal in
                             let uu____6204 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____6205 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___331_6203.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6204;
                               FStar_Tactics_Types.goal_ty = uu____6205;
                               FStar_Tactics_Types.opts =
                                 (uu___331_6203.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____6202] in
                         add_goals uu____6199))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6155
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6223 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____6223)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6240  ->
             let uu____6241 = FStar_Options.unsafe_tactic_exec () in
             if uu____6241
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6247  -> fun uu____6248  -> false) in
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
      let uu____6268 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____6268 with
      | (u,uu____6286,g_u) ->
          let g =
            let uu____6301 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6301;
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
      let uu____6316 = goal_of_goal_ty env typ in
      match uu____6316 with
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