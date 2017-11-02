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
  'Auu____75 .
    'Auu____75 tac ->
      FStar_Tactics_Types.proofstate ->
        'Auu____75 FStar_Tactics_Result.__result
  = fun t  -> fun p  -> t.tac_f p
let ret: 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p))
let bind: 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____136 = run t1 p in
           match uu____136 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____143 = t2 a in run uu____143 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: FStar_Tactics_Types.goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____154 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____154
        (FStar_Syntax_Print.binders_to_string ", ") in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
    let uu____157 =
      FStar_TypeChecker_Normalize.term_to_string
        g.FStar_Tactics_Types.context w in
    let uu____158 =
      FStar_TypeChecker_Normalize.term_to_string
        g.FStar_Tactics_Types.context t in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____157 uu____158
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____168 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____168
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____178 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____178
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____191 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____191
let comp_to_typ: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____196) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____206) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: FStar_Tactics_Types.goal -> Prims.bool =
  fun g  ->
    let uu____219 =
      let uu____224 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty in
      FStar_Syntax_Util.un_squash uu____224 in
    match uu____219 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____230 -> false
let dump_goal:
  'Auu____238 . 'Auu____238 -> FStar_Tactics_Types.goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____248 = goal_to_string goal in tacprint uu____248
let dump_cur: FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____256 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____260 = FStar_List.hd ps.FStar_Tactics_Types.goals in
            dump_goal ps uu____260))
let ps_to_string:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu____267  ->
    match uu____267 with
    | (msg,ps) ->
        let uu____274 =
          let uu____277 =
            let uu____278 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____278 msg in
          let uu____279 =
            let uu____282 =
              let uu____283 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range in
              FStar_Util.format1 "Position: %s\n" uu____283 in
            let uu____284 =
              let uu____287 =
                let uu____288 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals) in
                let uu____289 =
                  let uu____290 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals in
                  FStar_String.concat "\n" uu____290 in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____288
                  uu____289 in
              let uu____293 =
                let uu____296 =
                  let uu____297 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals) in
                  let uu____298 =
                    let uu____299 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals in
                    FStar_String.concat "\n" uu____299 in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____297
                    uu____298 in
                [uu____296] in
              uu____287 :: uu____293 in
            uu____282 :: uu____284 in
          uu____277 :: uu____279 in
        FStar_String.concat "" uu____274
let goal_to_json: FStar_Tactics_Types.goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____306 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____306 FStar_Syntax_Print.binders_to_json in
    let uu____307 =
      let uu____314 =
        let uu____321 =
          let uu____326 =
            let uu____327 =
              let uu____334 =
                let uu____339 =
                  let uu____340 =
                    FStar_TypeChecker_Normalize.term_to_string
                      g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness in
                  FStar_Util.JsonStr uu____340 in
                ("witness", uu____339) in
              let uu____341 =
                let uu____348 =
                  let uu____353 =
                    let uu____354 =
                      FStar_TypeChecker_Normalize.term_to_string
                        g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty in
                    FStar_Util.JsonStr uu____354 in
                  ("type", uu____353) in
                [uu____348] in
              uu____334 :: uu____341 in
            FStar_Util.JsonAssoc uu____327 in
          ("goal", uu____326) in
        [uu____321] in
      ("hyps", g_binders) :: uu____314 in
    FStar_Util.JsonAssoc uu____307
let ps_to_json:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____385  ->
    match uu____385 with
    | (msg,ps) ->
        let uu____392 =
          let uu____399 =
            let uu____406 =
              let uu____411 =
                let uu____412 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals in
                FStar_Util.JsonList uu____412 in
              ("goals", uu____411) in
            let uu____415 =
              let uu____422 =
                let uu____427 =
                  let uu____428 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals in
                  FStar_Util.JsonList uu____428 in
                ("smt-goals", uu____427) in
              [uu____422] in
            uu____406 :: uu____415 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____399 in
        FStar_Util.JsonAssoc uu____392
let dump_proofstate:
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____455  ->
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
         (let uu____476 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_cur uu____476 msg);
         FStar_Tactics_Result.Success ((), ps))
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc in
         (let uu____492 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_proofstate uu____492 msg);
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
      let uu____521 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____521 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____575 =
              let uu____578 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____578 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____575);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'Auu____663 . Prims.string -> 'Auu____663 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____674 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____674
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____679 . Prims.string -> Prims.string -> 'Auu____679 tac =
  fun msg  ->
    fun x  -> let uu____690 = FStar_Util.format1 msg x in fail uu____690
let fail2:
  'Auu____695 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____695 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____710 = FStar_Util.format2 msg x y in fail uu____710
let fail3:
  'Auu____716 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____716 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____735 = FStar_Util.format3 msg x y z in fail uu____735
let trytac': 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____765 = run t ps in
         match uu____765 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____786) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____811 = trytac' t in
    bind uu____811
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____838 -> ret FStar_Pervasives_Native.None)
let wrap_err: 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____864 = run t ps in
           match uu____864 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____881  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____896 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____908 =
         let uu___366_909 = p in
         let uu____910 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___366_909.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___366_909.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___366_909.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____910;
           FStar_Tactics_Types.smt_goals =
             (uu___366_909.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___366_909.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___366_909.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___366_909.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___366_909.FStar_Tactics_Types.entry_range)
         } in
       set uu____908)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____923 = trysolve goal solution in
      if uu____923
      then dismiss
      else
        (let uu____927 =
           let uu____928 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____929 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____930 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____928 uu____929
             uu____930 in
         fail uu____927)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___367_937 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___367_937.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___367_937.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___367_937.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___367_937.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___367_937.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___367_937.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___367_937.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___367_937.FStar_Tactics_Types.entry_range)
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
      let uu____961 = FStar_TypeChecker_Env.pop_bv e in
      match uu____961 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____979 =
      (let uu____982 = aux b2 env in Prims.op_Negation uu____982) &&
        (let uu____984 = FStar_ST.op_Bang nwarn in
         uu____984 < (Prims.parse_int "5")) in
    if uu____979
    then
      ((let uu____1032 =
          let uu____1033 = goal_to_string g in
          FStar_Util.format1
            "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
            uu____1033 in
        FStar_Errors.warn
          (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____1032);
       (let uu____1034 =
          let uu____1035 = FStar_ST.op_Bang nwarn in
          uu____1035 + (Prims.parse_int "1") in
        FStar_ST.op_Colon_Equals nwarn uu____1034))
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___368_1146 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___368_1146.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___368_1146.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___368_1146.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___368_1146.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___368_1146.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___368_1146.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___368_1146.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___368_1146.FStar_Tactics_Types.entry_range)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___369_1164 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___369_1164.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___369_1164.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___369_1164.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___369_1164.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___369_1164.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___369_1164.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___369_1164.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___369_1164.FStar_Tactics_Types.entry_range)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___370_1182 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1182.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_1182.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_1182.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___370_1182.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_1182.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1182.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1182.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1182.FStar_Tactics_Types.entry_range)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___371_1200 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___371_1200.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___371_1200.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___371_1200.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___371_1200.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___371_1200.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___371_1200.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___371_1200.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___371_1200.FStar_Tactics_Types.entry_range)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1209  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___372_1221 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___372_1221.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___372_1221.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___372_1221.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___372_1221.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___372_1221.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___372_1221.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___372_1221.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___372_1221.FStar_Tactics_Types.entry_range)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1247 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1247 with
        | (u,uu____1263,g_u) ->
            let uu____1277 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1277 (fun uu____1281  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1285 = FStar_Syntax_Util.un_squash t in
    match uu____1285 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1295 =
          let uu____1296 = FStar_Syntax_Subst.compress t' in
          uu____1296.FStar_Syntax_Syntax.n in
        (match uu____1295 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1300 -> false)
    | uu____1301 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1309 = FStar_Syntax_Util.un_squash t in
    match uu____1309 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1319 =
          let uu____1320 = FStar_Syntax_Subst.compress t' in
          uu____1320.FStar_Syntax_Syntax.n in
        (match uu____1319 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1324 -> false)
    | uu____1325 -> false
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
          let uu____1363 = new_uvar reason env typ in
          bind uu____1363
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
             let uu____1419 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1419
           with | e1 -> fail "not typeable")
let must_trivial: env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1467 =
          let uu____1468 =
            let uu____1469 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1469 in
          Prims.op_Negation uu____1468 in
        if uu____1467 then fail "got non-trivial guard" else ret ()
      with | uu____1478 -> fail "got non-trivial guard"
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1486 =
      bind cur_goal
        (fun goal  ->
           let uu____1492 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1492
             (fun uu____1512  ->
                match uu____1512 with
                | (t1,typ,guard) ->
                    let uu____1524 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____1524 (fun uu____1528  -> ret typ))) in
    FStar_All.pipe_left (wrap_err "tc") uu____1486
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1549 = mk_irrelevant_goal reason env phi opts in
          bind uu____1549 (fun goal  -> add_goals [goal])
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
       let uu____1569 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1569
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1573 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1573))
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
          let uu____1590 =
            let uu____1591 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1591.FStar_TypeChecker_Env.guard_f in
          match uu____1590 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1595 = istrivial e f in
              if uu____1595
              then ret ()
              else
                (let uu____1599 = mk_irrelevant_goal reason e f opts in
                 bind uu____1599
                   (fun goal  ->
                      let goal1 =
                        let uu___377_1606 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___377_1606.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___377_1606.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___377_1606.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___377_1606.FStar_Tactics_Types.opts);
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
          let uu____1627 =
            let uu____1628 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1628.FStar_TypeChecker_Env.guard_f in
          match uu____1627 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1636 = istrivial e f in
              if uu____1636
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1644 = mk_irrelevant_goal reason e f opts in
                 bind uu____1644
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___378_1654 = goal in
                            {
                              FStar_Tactics_Types.context =
                                (uu___378_1654.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___378_1654.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___378_1654.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___378_1654.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1660 = is_irrelevant g in
       if uu____1660
       then bind dismiss (fun uu____1664  -> add_smt_goals [g])
       else
         (let uu____1666 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1666))
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
             let uu____1707 =
               try
                 let uu____1741 =
                   let uu____1750 = FStar_BigInt.to_int_fs n1 in
                   FStar_List.splitAt uu____1750 p.FStar_Tactics_Types.goals in
                 ret uu____1741
               with | uu____1772 -> fail "divide: not enough goals" in
             bind uu____1707
               (fun uu____1799  ->
                  match uu____1799 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___379_1825 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___379_1825.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___379_1825.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___379_1825.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___379_1825.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___379_1825.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___379_1825.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___379_1825.FStar_Tactics_Types.entry_range)
                        } in
                      let rp =
                        let uu___380_1827 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___380_1827.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___380_1827.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___380_1827.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___380_1827.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___380_1827.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___380_1827.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___380_1827.FStar_Tactics_Types.entry_range)
                        } in
                      let uu____1828 = set lp in
                      bind uu____1828
                        (fun uu____1836  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1850 = set rp in
                                     bind uu____1850
                                       (fun uu____1858  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___381_1874 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___381_1874.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___381_1874.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___381_1874.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___381_1874.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___381_1874.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___381_1874.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___381_1874.FStar_Tactics_Types.entry_range)
                                                      } in
                                                    let uu____1875 = set p' in
                                                    bind uu____1875
                                                      (fun uu____1883  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1901 = divide FStar_BigInt.one f idtac in
    bind uu____1901
      (fun uu____1914  -> match uu____1914 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1948::uu____1949 ->
             let uu____1952 =
               let uu____1961 = map tau in
               divide FStar_BigInt.one tau uu____1961 in
             bind uu____1952
               (fun uu____1979  ->
                  match uu____1979 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____2016 =
        bind t1
          (fun uu____2021  ->
             let uu____2022 = map t2 in
             bind uu____2022 (fun uu____2030  -> ret ())) in
      focus uu____2016
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____2041 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____2041 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2056 =
             let uu____2057 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____2057 in
           if uu____2056
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____2063 = new_uvar "intro" env' typ' in
              bind uu____2063
                (fun u  ->
                   let uu____2070 =
                     let uu____2071 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____2071 in
                   if uu____2070
                   then
                     let uu____2074 =
                       let uu____2077 =
                         let uu___384_2078 = goal in
                         let uu____2079 = bnorm env' u in
                         let uu____2080 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2079;
                           FStar_Tactics_Types.goal_ty = uu____2080;
                           FStar_Tactics_Types.opts =
                             (uu___384_2078.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___384_2078.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____2077 in
                     bind uu____2074 (fun uu____2082  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2088 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____2088)
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
       (let uu____2109 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____2109 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2128 =
              let uu____2129 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____2129 in
            if uu____2128
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____2145 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____2145; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____2147 =
                 let uu____2150 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____2150 in
               bind uu____2147
                 (fun u  ->
                    let lb =
                      let uu____2166 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2166 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2170 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2170 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2207 =
                            let uu____2210 =
                              let uu___385_2211 = goal in
                              let uu____2212 = bnorm env' u in
                              let uu____2213 =
                                let uu____2214 = comp_to_typ c in
                                bnorm env' uu____2214 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2212;
                                FStar_Tactics_Types.goal_ty = uu____2213;
                                FStar_Tactics_Types.opts =
                                  (uu___385_2211.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___385_2211.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2210 in
                          bind uu____2207
                            (fun uu____2221  ->
                               let uu____2222 =
                                 let uu____2227 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2227, b) in
                               ret uu____2222)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2241 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2241))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2265 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2265 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___386_2272 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___386_2272.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___386_2272.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___386_2272.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2290 =
          bind get
            (fun ps  ->
               let uu____2296 = __tc e t in
               bind uu____2296
                 (fun uu____2318  ->
                    match uu____2318 with
                    | (t1,uu____2328,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2334 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2334 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2290
let refine_intro: Prims.unit tac =
  let uu____2344 =
    bind cur_goal
      (fun g  ->
         let uu____2351 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
         match uu____2351 with
         | (uu____2364,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___387_2389 = g in
               {
                 FStar_Tactics_Types.context =
                   (uu___387_2389.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___387_2389.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___387_2389.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___387_2389.FStar_Tactics_Types.is_guard)
               } in
             let uu____2390 =
               let uu____2395 =
                 let uu____2400 =
                   let uu____2401 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2401] in
                 FStar_Syntax_Subst.open_term uu____2400 phi in
               match uu____2395 with
               | (bvs,phi1) ->
                   let uu____2408 =
                     let uu____2409 = FStar_List.hd bvs in
                     FStar_Pervasives_Native.fst uu____2409 in
                   (uu____2408, phi1) in
             (match uu____2390 with
              | (bv1,phi1) ->
                  let uu____2422 =
                    let uu____2425 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1 in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2425
                      g.FStar_Tactics_Types.opts in
                  bind uu____2422
                    (fun g2  ->
                       bind dismiss (fun uu____2429  -> add_goals [g1; g2])))) in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2344
let __exact_now: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun force_guard  ->
    fun t  ->
      bind cur_goal
        (fun goal  ->
           let uu____2447 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____2447
             (fun uu____2467  ->
                match uu____2467 with
                | (t1,typ,guard) ->
                    let uu____2479 =
                      if force_guard
                      then
                        must_trivial goal.FStar_Tactics_Types.context guard
                      else
                        add_goal_from_guard "__exact typing"
                          goal.FStar_Tactics_Types.context guard
                          goal.FStar_Tactics_Types.opts in
                    bind uu____2479
                      (fun uu____2487  ->
                         let uu____2488 =
                           do_unify goal.FStar_Tactics_Types.context typ
                             goal.FStar_Tactics_Types.goal_ty in
                         if uu____2488
                         then solve goal t1
                         else
                           (let uu____2492 =
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context t1 in
                            let uu____2493 =
                              let uu____2494 =
                                bnorm goal.FStar_Tactics_Types.context typ in
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context uu____2494 in
                            let uu____2495 =
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context
                                goal.FStar_Tactics_Types.goal_ty in
                            fail3
                              "%s : %s does not exactly solve the goal %s"
                              uu____2492 uu____2493 uu____2495))))
let __exact: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun force_guard  ->
    fun t  ->
      let uu____2506 =
        let uu____2513 = __exact_now force_guard t in trytac' uu____2513 in
      bind uu____2506
        (fun uu___361_2522  ->
           match uu___361_2522 with
           | FStar_Util.Inr r -> ret ()
           | FStar_Util.Inl e ->
               let uu____2531 =
                 let uu____2538 =
                   let uu____2541 = norm [FStar_Syntax_Embeddings.Delta] in
                   bind uu____2541
                     (fun uu____2545  ->
                        bind refine_intro
                          (fun uu____2547  -> __exact_now force_guard t)) in
                 trytac' uu____2538 in
               bind uu____2531
                 (fun uu___360_2554  ->
                    match uu___360_2554 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl uu____2562 -> fail e))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2570 =
      mlog
        (fun uu____2575  ->
           let uu____2576 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact: tm = %s\n" uu____2576)
        (fun uu____2579  ->
           let uu____2580 = __exact true tm in focus uu____2580) in
    FStar_All.pipe_left (wrap_err "exact") uu____2570
let exact_guard: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2594 =
      mlog
        (fun uu____2599  ->
           let uu____2600 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact_guard: tm = %s\n" uu____2600)
        (fun uu____2603  ->
           let uu____2604 = __exact false tm in focus uu____2604) in
    FStar_All.pipe_left (wrap_err "exact_guard") uu____2594
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2621 =
             let uu____2628 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2628 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2621 in
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
          let uu____2688 = f x in
          bind uu____2688
            (fun y  ->
               let uu____2696 = mapM f xs in
               bind uu____2696 (fun ys  -> ret (y :: ys)))
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2714 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2731 =
               let uu____2736 = __exact true tm in trytac uu____2736 in
             bind uu____2731
               (fun uu___362_2743  ->
                  match uu___362_2743 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2749 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2749 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2781  ->
                                let uu____2782 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2782)
                             (fun uu____2785  ->
                                let uu____2786 =
                                  let uu____2787 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2787 in
                                if uu____2786
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2791 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2791
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2811 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2811 in
                                        let uu____2812 =
                                          __apply uopt tm' typ' in
                                        bind uu____2812
                                          (fun uu____2820  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2822 =
                                               let uu____2823 =
                                                 let uu____2826 =
                                                   let uu____2827 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2827 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2826 in
                                               uu____2823.FStar_Syntax_Syntax.n in
                                             match uu____2822 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2855) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2883 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2883
                                                      then ret ()
                                                      else
                                                        (let uu____2887 =
                                                           let uu____2890 =
                                                             let uu___388_2891
                                                               = goal in
                                                             let uu____2892 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2893 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___388_2891.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2892;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2893;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___388_2891.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2890] in
                                                         add_goals uu____2887))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2939 =
        mlog
          (fun uu____2944  ->
             let uu____2945 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2945)
          (fun uu____2947  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2951 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2951
                    (fun uu____2972  ->
                       match uu____2972 with
                       | (tm1,typ,guard) ->
                           let uu____2984 =
                             let uu____2987 =
                               let uu____2990 = __apply uopt tm1 typ in
                               bind uu____2990
                                 (fun uu____2994  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2987 in
                           let uu____2995 =
                             let uu____2998 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context tm1 in
                             let uu____2999 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context typ in
                             let uu____3000 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2998 uu____2999 uu____3000 in
                           try_unif uu____2984 uu____2995))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2939
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____3012 =
      let uu____3015 =
        mlog
          (fun uu____3020  ->
             let uu____3021 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3021)
          (fun uu____3024  ->
             let is_unit_t t =
               let uu____3029 =
                 let uu____3030 = FStar_Syntax_Subst.compress t in
                 uu____3030.FStar_Syntax_Syntax.n in
               match uu____3029 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3034 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____3038 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____3038
                    (fun uu____3060  ->
                       match uu____3060 with
                       | (tm1,t,guard) ->
                           let uu____3072 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____3072 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3102 =
                                     FStar_List.fold_left
                                       (fun uu____3148  ->
                                          fun uu____3149  ->
                                            match (uu____3148, uu____3149)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____3252 =
                                                  is_unit_t b_t in
                                                if uu____3252
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3290 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____3290 with
                                                   | (u,uu____3320,g_u) ->
                                                       let uu____3334 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____3334,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____3102 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3404 =
                                         let uu____3413 =
                                           let uu____3422 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3422.FStar_Syntax_Syntax.effect_args in
                                         match uu____3413 with
                                         | pre::post::uu____3433 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3474 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3404 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3506 =
                                                let uu____3515 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3515] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3506 in
                                            let uu____3516 =
                                              let uu____3517 =
                                                let uu____3518 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3518
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3517 in
                                            if uu____3516
                                            then
                                              let uu____3521 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3522 =
                                                let uu____3523 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3523 in
                                              let uu____3524 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3521 uu____3522
                                                uu____3524
                                            else
                                              (let solution =
                                                 let uu____3527 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3527 in
                                               let uu____3528 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3528
                                                 (fun uu____3533  ->
                                                    let uu____3534 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit in
                                                    bind uu____3534
                                                      (fun uu____3542  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3553 =
                                                               let uu____3560
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3560 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3553 in
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
                                                           let uu____3601 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3601
                                                           with
                                                           | (hd1,uu____3617)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3639)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3664
                                                                    -> false) in
                                                         let uu____3665 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3737
                                                                    ->
                                                                   match uu____3737
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3765)
                                                                    ->
                                                                    let uu____3766
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____3766
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3792)
                                                                    ->
                                                                    let uu____3813
                                                                    =
                                                                    let uu____3814
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3814.FStar_Syntax_Syntax.n in
                                                                    (match uu____3813
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3827
                                                                    ->
                                                                    let uu____3844
                                                                    =
                                                                    let uu____3853
                                                                    =
                                                                    let uu____3856
                                                                    =
                                                                    let uu___391_3857
                                                                    = goal in
                                                                    let uu____3858
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3859
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___391_3857.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3858;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3859;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___391_3857.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___391_3857.FStar_Tactics_Types.is_guard)
                                                                    } in
                                                                    [uu____3856] in
                                                                    (uu____3853,
                                                                    []) in
                                                                    ret
                                                                    uu____3844
                                                                    | 
                                                                    uu____3872
                                                                    ->
                                                                    let term1
                                                                    =
                                                                    bnorm env
                                                                    term in
                                                                    let uu____3874
                                                                    =
                                                                    let uu____3881
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3881
                                                                    term1 in
                                                                    (match uu____3874
                                                                    with
                                                                    | 
                                                                    (uu____3892,uu____3893,g_typ)
                                                                    ->
                                                                    let uu____3895
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts in
                                                                    bind
                                                                    uu____3895
                                                                    (fun
                                                                    uu___363_3911
                                                                     ->
                                                                    match uu___363_3911
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
                                                         bind uu____3665
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3979
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3979 in
                                                              let smt_goals =
                                                                let uu____4001
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____4001 in
                                                              let rec filter'
                                                                f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4057
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____4057
                                                                    then
                                                                    let uu____4060
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____4060
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                              let sub_goals1
                                                                =
                                                                filter'
                                                                  (fun g  ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4074
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____4074)
                                                                  sub_goals in
                                                              let uu____4075
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts in
                                                              bind uu____4075
                                                                (fun
                                                                   uu____4080
                                                                    ->
                                                                   let uu____4081
                                                                    =
                                                                    let uu____4084
                                                                    =
                                                                    let uu____4085
                                                                    =
                                                                    let uu____4086
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4086 in
                                                                    Prims.op_Negation
                                                                    uu____4085 in
                                                                    if
                                                                    uu____4084
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret () in
                                                                   bind
                                                                    uu____4081
                                                                    (fun
                                                                    uu____4092
                                                                     ->
                                                                    let uu____4093
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals in
                                                                    bind
                                                                    uu____4093
                                                                    (fun
                                                                    uu____4097
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))) in
      focus uu____3015 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3012
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4117 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____4117 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4127::(e1,uu____4129)::(e2,uu____4131)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4190 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4212 = destruct_eq' typ in
    match uu____4212 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4242 = FStar_Syntax_Util.un_squash typ in
        (match uu____4242 with
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
        let uu____4298 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____4298 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4346 = aux e' in
               FStar_Util.map_opt uu____4346
                 (fun uu____4370  ->
                    match uu____4370 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____4391 = aux e in
      FStar_Util.map_opt uu____4391
        (fun uu____4415  ->
           match uu____4415 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____4470 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____4470
            (fun uu____4494  ->
               match uu____4494 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___392_4511 = bv in
                     let uu____4512 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___392_4511.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___392_4511.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4512
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___393_4521 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___393_4521.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___393_4521.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4534 = h in
         match uu____4534 with
         | (bv,uu____4538) ->
             mlog
               (fun uu____4542  ->
                  let uu____4543 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4544 =
                    FStar_Syntax_Print.term_to_string
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4543
                    uu____4544)
               (fun uu____4547  ->
                  let uu____4548 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4548 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4577 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4577 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4592 =
                             let uu____4593 = FStar_Syntax_Subst.compress x in
                             uu____4593.FStar_Syntax_Syntax.n in
                           (match uu____4592 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___394_4606 = bv1 in
                                  let uu____4607 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___394_4606.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___394_4606.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4607
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4613 =
                                  let uu___395_4614 = goal in
                                  let uu____4615 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4616 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4617 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4615;
                                    FStar_Tactics_Types.witness = uu____4616;
                                    FStar_Tactics_Types.goal_ty = uu____4617;
                                    FStar_Tactics_Types.opts =
                                      (uu___395_4614.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___395_4614.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4613
                            | uu____4618 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4619 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4644 = b in
           match uu____4644 with
           | (bv,uu____4648) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___396_4652 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___396_4652.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___396_4652.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4656 =
                   let uu____4657 =
                     let uu____4664 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4664) in
                   FStar_Syntax_Syntax.NT uu____4657 in
                 [uu____4656] in
               let uu____4665 = subst_goal bv bv' s1 goal in
               (match uu____4665 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4684 = b in
         match uu____4684 with
         | (bv,uu____4688) ->
             let uu____4689 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4689 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4718 = FStar_Syntax_Util.type_u () in
                  (match uu____4718 with
                   | (ty,u) ->
                       let uu____4727 = new_uvar "binder_retype" e0 ty in
                       bind uu____4727
                         (fun t'  ->
                            let bv'' =
                              let uu___397_4737 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___397_4737.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___397_4737.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4741 =
                                let uu____4742 =
                                  let uu____4749 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4749) in
                                FStar_Syntax_Syntax.NT uu____4742 in
                              [uu____4741] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___398_4757 = b1 in
                                   let uu____4758 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___398_4757.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___398_4757.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4758
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4764  ->
                                 let uu____4765 =
                                   let uu____4768 =
                                     let uu____4771 =
                                       let uu___399_4772 = goal in
                                       let uu____4773 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4774 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4773;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4774;
                                         FStar_Tactics_Types.opts =
                                           (uu___399_4772.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___399_4772.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4771] in
                                   add_goals uu____4768 in
                                 bind uu____4765
                                   (fun uu____4777  ->
                                      let uu____4778 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4778
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4799 = b in
           match uu____4799 with
           | (bv,uu____4803) ->
               let uu____4804 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4804 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4836 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4836 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___400_4841 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___400_4841.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___400_4841.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___401_4845 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___401_4845.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___401_4845.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___401_4845.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___401_4845.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4851 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4851 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4873 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4873 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___402_4907 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___402_4907.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___402_4907.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4918 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4918 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4939 = FStar_Syntax_Print.bv_to_string x in
               let uu____4940 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4939 uu____4940
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4947 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4947 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4969 = FStar_Util.set_mem x fns_ty in
           if uu____4969
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4973 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4973
                (fun u  ->
                   let uu____4979 =
                     let uu____4980 = trysolve goal u in
                     Prims.op_Negation uu____4980 in
                   if uu____4979
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___403_4985 = goal in
                        let uu____4986 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4986;
                          FStar_Tactics_Types.goal_ty =
                            (uu___403_4985.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___403_4985.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___403_4985.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4988  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4999 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4999 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____5023  ->
                    let uu____5024 = clear b in
                    bind uu____5024
                      (fun uu____5028  ->
                         bind intro (fun uu____5030  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___404_5046 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___404_5046.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___404_5046.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___404_5046.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___404_5046.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5048  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___405_5064 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___405_5064.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___405_5064.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___405_5064.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___405_5064.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5066  -> add_goals [g']))
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
            let uu____5098 = FStar_Syntax_Subst.compress t in
            uu____5098.FStar_Syntax_Syntax.n in
          let uu____5101 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___407_5107 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___407_5107.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___407_5107.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____5101
            (fun t1  ->
               let tn1 =
                 let uu____5115 =
                   let uu____5116 = FStar_Syntax_Subst.compress t1 in
                   uu____5116.FStar_Syntax_Syntax.n in
                 match uu____5115 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____5148 = ff hd1 in
                     bind uu____5148
                       (fun hd2  ->
                          let fa uu____5168 =
                            match uu____5168 with
                            | (a,q) ->
                                let uu____5181 = ff a in
                                bind uu____5181 (fun a1  -> ret (a1, q)) in
                          let uu____5194 = mapM fa args in
                          bind uu____5194
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5254 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____5254 with
                      | (bs1,t') ->
                          let uu____5263 =
                            let uu____5266 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____5266 t' in
                          bind uu____5263
                            (fun t''  ->
                               let uu____5270 =
                                 let uu____5271 =
                                   let uu____5288 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____5289 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____5288, uu____5289, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____5271 in
                               ret uu____5270))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5310 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___406_5317 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___406_5317.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___406_5317.FStar_Syntax_Syntax.vars)
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
            let uu____5346 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____5346 with
            | (t1,lcomp,g) ->
                let uu____5358 =
                  (let uu____5361 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____5361) ||
                    (let uu____5363 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____5363) in
                if uu____5358
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____5373 = new_uvar "pointwise_rec" env typ in
                     bind uu____5373
                       (fun ut  ->
                          log ps
                            (fun uu____5384  ->
                               let uu____5385 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____5386 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5385 uu____5386);
                          (let uu____5387 =
                             let uu____5390 =
                               let uu____5391 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____5391 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5390 opts in
                           bind uu____5387
                             (fun uu____5394  ->
                                let uu____5395 =
                                  bind tau
                                    (fun uu____5401  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____5407  ->
                                            let uu____5408 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____5409 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5408 uu____5409);
                                       ret ut1) in
                                focus uu____5395))) in
                   let uu____5410 = trytac' rewrite_eq in
                   bind uu____5410
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
           let uu____5452 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5452 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5489  ->
                     let uu____5490 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5490);
                bind dismiss_all
                  (fun uu____5493  ->
                     let uu____5494 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5494
                       (fun gt'  ->
                          log ps
                            (fun uu____5504  ->
                               let uu____5505 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5505);
                          (let uu____5506 = push_goals gs in
                           bind uu____5506
                             (fun uu____5510  ->
                                add_goals
                                  [(let uu___408_5512 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___408_5512.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___408_5512.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___408_5512.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___408_5512.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5532 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5532 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5544 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5544 with
            | (hd1,args) ->
                let uu____5577 =
                  let uu____5590 =
                    let uu____5591 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5591.FStar_Syntax_Syntax.n in
                  (uu____5590, args) in
                (match uu____5577 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5605::(l,uu____5607)::(r,uu____5609)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5656 =
                       let uu____5657 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5657 in
                     if uu____5656
                     then
                       let uu____5660 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____5661 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5660 uu____5661
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5664) ->
                     let uu____5681 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5681))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5689 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5689
         (fun u  ->
            let g' =
              let uu___409_5696 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___409_5696.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___409_5696.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___409_5696.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___409_5696.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5699  ->
                 let uu____5700 =
                   let uu____5703 =
                     let uu____5704 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5704
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5703
                     g.FStar_Tactics_Types.opts in
                 bind uu____5700
                   (fun uu____5707  ->
                      let uu____5708 = add_goals [g'] in
                      bind uu____5708 (fun uu____5712  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___410_5729 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___410_5729.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___410_5729.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___410_5729.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___410_5729.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___410_5729.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___410_5729.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___410_5729.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___410_5729.FStar_Tactics_Types.entry_range)
              })
       | uu____5730 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___411_5745 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___411_5745.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___411_5745.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___411_5745.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___411_5745.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___411_5745.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___411_5745.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___411_5745.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___411_5745.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5752 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5770 =
      bind cur_goal
        (fun g  ->
           let uu____5784 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5784
             (fun uu____5820  ->
                match uu____5820 with
                | (t1,typ,guard) ->
                    let uu____5836 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5836 with
                     | (hd1,args) ->
                         let uu____5879 =
                           let uu____5892 =
                             let uu____5893 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5893.FStar_Syntax_Syntax.n in
                           (uu____5892, args) in
                         (match uu____5879 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5912)::(q,uu____5914)::[]) when
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
                                let uu___412_5952 = g in
                                let uu____5953 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5953;
                                  FStar_Tactics_Types.witness =
                                    (uu___412_5952.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___412_5952.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___412_5952.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___412_5952.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___413_5955 = g in
                                let uu____5956 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5956;
                                  FStar_Tactics_Types.witness =
                                    (uu___413_5955.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___413_5955.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___413_5955.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___413_5955.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5963  ->
                                   let uu____5964 = add_goals [g1; g2] in
                                   bind uu____5964
                                     (fun uu____5973  ->
                                        let uu____5974 =
                                          let uu____5979 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5980 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5979, uu____5980) in
                                        ret uu____5974))
                          | uu____5985 ->
                              let uu____5998 =
                                FStar_TypeChecker_Normalize.term_to_string
                                  g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5998)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5770
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6036 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____6036);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___414_6043 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___414_6043.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___414_6043.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___414_6043.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___414_6043.FStar_Tactics_Types.is_guard)
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
      let uu____6079 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____6087 = __tc env tm in
             bind uu____6087
               (fun uu____6107  ->
                  match uu____6107 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____6079
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____6138 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6144 =
              let uu____6145 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6145 in
            new_uvar "uvar_env.2" env uu____6144 in
      bind uu____6138
        (fun typ  ->
           let uu____6157 = new_uvar "uvar_env" env typ in
           bind uu____6157 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____6169 =
      bind cur_goal
        (fun goal  ->
           let uu____6175 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____6175
             (fun uu____6195  ->
                match uu____6195 with
                | (t1,typ,guard) ->
                    let uu____6207 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____6207
                      (fun uu____6212  ->
                         let uu____6213 =
                           let uu____6216 =
                             let uu___415_6217 = goal in
                             let uu____6218 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____6219 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___415_6217.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6218;
                               FStar_Tactics_Types.goal_ty = uu____6219;
                               FStar_Tactics_Types.opts =
                                 (uu___415_6217.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____6216] in
                         add_goals uu____6213))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6169
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6237 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____6237)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6254  ->
             let uu____6255 = FStar_Options.unsafe_tactic_exec () in
             if uu____6255
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6261  -> fun uu____6262  -> false) in
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
      let uu____6282 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____6282 with
      | (u,uu____6300,g_u) ->
          let g =
            let uu____6315 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6315;
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
      let uu____6330 = goal_of_goal_ty env typ in
      match uu____6330 with
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