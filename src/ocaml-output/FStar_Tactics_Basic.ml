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
         | uu____1947::uu____1948 ->
             let uu____1951 =
               let uu____1960 = map tau in
               divide FStar_BigInt.one tau uu____1960 in
             bind uu____1951
               (fun uu____1978  ->
                  match uu____1978 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____2015 =
        bind t1
          (fun uu____2020  ->
             let uu____2021 = map t2 in
             bind uu____2021 (fun uu____2029  -> ret ())) in
      focus uu____2015
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____2040 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____2040 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2055 =
             let uu____2056 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____2056 in
           if uu____2055
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____2062 = new_uvar "intro" env' typ' in
              bind uu____2062
                (fun u  ->
                   let uu____2069 =
                     let uu____2070 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____2070 in
                   if uu____2069
                   then
                     let uu____2073 =
                       let uu____2076 =
                         let uu___384_2077 = goal in
                         let uu____2078 = bnorm env' u in
                         let uu____2079 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2078;
                           FStar_Tactics_Types.goal_ty = uu____2079;
                           FStar_Tactics_Types.opts =
                             (uu___384_2077.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___384_2077.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____2076 in
                     bind uu____2073 (fun uu____2081  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2087 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____2087)
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
       (let uu____2108 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____2108 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2127 =
              let uu____2128 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____2128 in
            if uu____2127
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____2144 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____2144; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____2146 =
                 let uu____2149 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____2149 in
               bind uu____2146
                 (fun u  ->
                    let lb =
                      let uu____2165 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2165 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2169 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2169 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2206 =
                            let uu____2209 =
                              let uu___385_2210 = goal in
                              let uu____2211 = bnorm env' u in
                              let uu____2212 =
                                let uu____2213 = comp_to_typ c in
                                bnorm env' uu____2213 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2211;
                                FStar_Tactics_Types.goal_ty = uu____2212;
                                FStar_Tactics_Types.opts =
                                  (uu___385_2210.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___385_2210.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2209 in
                          bind uu____2206
                            (fun uu____2220  ->
                               let uu____2221 =
                                 let uu____2226 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2226, b) in
                               ret uu____2221)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2240 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2240))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2264 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2264 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___386_2271 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___386_2271.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___386_2271.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___386_2271.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2289 =
          bind get
            (fun ps  ->
               let uu____2295 = __tc e t in
               bind uu____2295
                 (fun uu____2317  ->
                    match uu____2317 with
                    | (t1,uu____2327,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2333 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2333 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2289
let refine_intro: Prims.unit tac =
  let uu____2343 =
    bind cur_goal
      (fun g  ->
         let uu____2350 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
         match uu____2350 with
         | (uu____2363,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___387_2388 = g in
               {
                 FStar_Tactics_Types.context =
                   (uu___387_2388.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___387_2388.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___387_2388.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___387_2388.FStar_Tactics_Types.is_guard)
               } in
             let uu____2389 =
               let uu____2394 =
                 let uu____2399 =
                   let uu____2400 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2400] in
                 FStar_Syntax_Subst.open_term uu____2399 phi in
               match uu____2394 with
               | (bvs,phi1) ->
                   let uu____2407 =
                     let uu____2408 = FStar_List.hd bvs in
                     FStar_Pervasives_Native.fst uu____2408 in
                   (uu____2407, phi1) in
             (match uu____2389 with
              | (bv1,phi1) ->
                  let uu____2421 =
                    let uu____2424 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1 in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2424
                      g.FStar_Tactics_Types.opts in
                  bind uu____2421
                    (fun g2  ->
                       bind dismiss (fun uu____2428  -> add_goals [g1; g2])))) in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2343
let __exact_now: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun force_guard  ->
    fun t  ->
      bind cur_goal
        (fun goal  ->
           let uu____2446 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____2446
             (fun uu____2466  ->
                match uu____2466 with
                | (t1,typ,guard) ->
                    let uu____2478 =
                      if force_guard
                      then
                        must_trivial goal.FStar_Tactics_Types.context guard
                      else
                        add_goal_from_guard "__exact typing"
                          goal.FStar_Tactics_Types.context guard
                          goal.FStar_Tactics_Types.opts in
                    bind uu____2478
                      (fun uu____2486  ->
                         let uu____2487 =
                           do_unify goal.FStar_Tactics_Types.context typ
                             goal.FStar_Tactics_Types.goal_ty in
                         if uu____2487
                         then solve goal t1
                         else
                           (let uu____2491 =
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context t1 in
                            let uu____2492 =
                              let uu____2493 =
                                bnorm goal.FStar_Tactics_Types.context typ in
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context uu____2493 in
                            let uu____2494 =
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context
                                goal.FStar_Tactics_Types.goal_ty in
                            fail3
                              "%s : %s does not exactly solve the goal %s"
                              uu____2491 uu____2492 uu____2494))))
let __exact: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun force_guard  ->
    fun t  ->
      let uu____2505 =
        let uu____2512 = __exact_now force_guard t in trytac' uu____2512 in
      bind uu____2505
        (fun uu___361_2521  ->
           match uu___361_2521 with
           | FStar_Util.Inr r -> ret ()
           | FStar_Util.Inl e ->
               let uu____2530 =
                 let uu____2537 =
                   let uu____2540 = norm [FStar_Syntax_Embeddings.Delta] in
                   bind uu____2540
                     (fun uu____2544  ->
                        bind refine_intro
                          (fun uu____2546  -> __exact_now force_guard t)) in
                 trytac' uu____2537 in
               bind uu____2530
                 (fun uu___360_2553  ->
                    match uu___360_2553 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl uu____2561 -> fail e))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2569 =
      mlog
        (fun uu____2574  ->
           let uu____2575 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact: tm = %s\n" uu____2575)
        (fun uu____2578  ->
           let uu____2579 = __exact true tm in focus uu____2579) in
    FStar_All.pipe_left (wrap_err "exact") uu____2569
let exact_guard: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2593 =
      mlog
        (fun uu____2598  ->
           let uu____2599 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact_guard: tm = %s\n" uu____2599)
        (fun uu____2602  ->
           let uu____2603 = __exact false tm in focus uu____2603) in
    FStar_All.pipe_left (wrap_err "exact_guard") uu____2593
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2620 =
             let uu____2627 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2627 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2620 in
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
          let uu____2685 = f x in
          bind uu____2685
            (fun y  ->
               let uu____2693 = mapM f xs in
               bind uu____2693 (fun ys  -> ret (y :: ys)))
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2711 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2728 =
               let uu____2733 = __exact true tm in trytac uu____2733 in
             bind uu____2728
               (fun uu___362_2740  ->
                  match uu___362_2740 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2746 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2746 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2778  ->
                                let uu____2779 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2779)
                             (fun uu____2782  ->
                                let uu____2783 =
                                  let uu____2784 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2784 in
                                if uu____2783
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2788 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2788
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2808 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2808 in
                                        let uu____2809 =
                                          __apply uopt tm' typ' in
                                        bind uu____2809
                                          (fun uu____2817  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2819 =
                                               let uu____2820 =
                                                 let uu____2823 =
                                                   let uu____2824 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2824 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2823 in
                                               uu____2820.FStar_Syntax_Syntax.n in
                                             match uu____2819 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2852) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2880 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2880
                                                      then ret ()
                                                      else
                                                        (let uu____2884 =
                                                           let uu____2887 =
                                                             let uu___388_2888
                                                               = goal in
                                                             let uu____2889 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2890 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___388_2888.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2889;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2890;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___388_2888.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2887] in
                                                         add_goals uu____2884))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2936 =
        mlog
          (fun uu____2941  ->
             let uu____2942 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2942)
          (fun uu____2944  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2948 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2948
                    (fun uu____2969  ->
                       match uu____2969 with
                       | (tm1,typ,guard) ->
                           let uu____2981 =
                             let uu____2984 =
                               let uu____2987 = __apply uopt tm1 typ in
                               bind uu____2987
                                 (fun uu____2991  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2984 in
                           let uu____2992 =
                             let uu____2995 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context tm1 in
                             let uu____2996 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context typ in
                             let uu____2997 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2995 uu____2996 uu____2997 in
                           try_unif uu____2981 uu____2992))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2936
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____3009 =
      let uu____3012 =
        mlog
          (fun uu____3017  ->
             let uu____3018 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3018)
          (fun uu____3021  ->
             let is_unit_t t =
               let uu____3026 =
                 let uu____3027 = FStar_Syntax_Subst.compress t in
                 uu____3027.FStar_Syntax_Syntax.n in
               match uu____3026 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3031 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____3035 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____3035
                    (fun uu____3057  ->
                       match uu____3057 with
                       | (tm1,t,guard) ->
                           let uu____3069 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____3069 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3099 =
                                     FStar_List.fold_left
                                       (fun uu____3145  ->
                                          fun uu____3146  ->
                                            match (uu____3145, uu____3146)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____3249 =
                                                  is_unit_t b_t in
                                                if uu____3249
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3287 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____3287 with
                                                   | (u,uu____3317,g_u) ->
                                                       let uu____3331 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____3331,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____3099 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3401 =
                                         let uu____3410 =
                                           let uu____3419 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3419.FStar_Syntax_Syntax.effect_args in
                                         match uu____3410 with
                                         | pre::post::uu____3430 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3471 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3401 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3503 =
                                                let uu____3512 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3512] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3503 in
                                            let uu____3513 =
                                              let uu____3514 =
                                                let uu____3515 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3515
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3514 in
                                            if uu____3513
                                            then
                                              let uu____3518 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3519 =
                                                let uu____3520 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3520 in
                                              let uu____3521 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3518 uu____3519
                                                uu____3521
                                            else
                                              (let solution =
                                                 let uu____3524 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3524 in
                                               let uu____3525 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3525
                                                 (fun uu____3530  ->
                                                    let uu____3531 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit in
                                                    bind uu____3531
                                                      (fun uu____3539  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3550 =
                                                               let uu____3557
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3557 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3550 in
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
                                                           let uu____3598 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3598
                                                           with
                                                           | (hd1,uu____3614)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3636)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3661
                                                                    -> false) in
                                                         let uu____3662 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3734
                                                                    ->
                                                                   match uu____3734
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3762)
                                                                    ->
                                                                    let uu____3763
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____3763
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3789)
                                                                    ->
                                                                    let uu____3810
                                                                    =
                                                                    let uu____3811
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3811.FStar_Syntax_Syntax.n in
                                                                    (match uu____3810
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3824
                                                                    ->
                                                                    let uu____3841
                                                                    =
                                                                    let uu____3850
                                                                    =
                                                                    let uu____3853
                                                                    =
                                                                    let uu___391_3854
                                                                    = goal in
                                                                    let uu____3855
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3856
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___391_3854.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3855;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3856;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___391_3854.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___391_3854.FStar_Tactics_Types.is_guard)
                                                                    } in
                                                                    [uu____3853] in
                                                                    (uu____3850,
                                                                    []) in
                                                                    ret
                                                                    uu____3841
                                                                    | 
                                                                    uu____3869
                                                                    ->
                                                                    let term1
                                                                    =
                                                                    bnorm env
                                                                    term in
                                                                    let uu____3871
                                                                    =
                                                                    let uu____3878
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3878
                                                                    term1 in
                                                                    (match uu____3871
                                                                    with
                                                                    | 
                                                                    (uu____3889,uu____3890,g_typ)
                                                                    ->
                                                                    let uu____3892
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts in
                                                                    bind
                                                                    uu____3892
                                                                    (fun
                                                                    uu___363_3908
                                                                     ->
                                                                    match uu___363_3908
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
                                                         bind uu____3662
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3976
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3976 in
                                                              let smt_goals =
                                                                let uu____3998
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3998 in
                                                              let rec filter'
                                                                f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4054
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____4054
                                                                    then
                                                                    let uu____4057
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____4057
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                              let sub_goals1
                                                                =
                                                                filter'
                                                                  (fun g  ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4071
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____4071)
                                                                  sub_goals in
                                                              let uu____4072
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts in
                                                              bind uu____4072
                                                                (fun
                                                                   uu____4077
                                                                    ->
                                                                   let uu____4078
                                                                    =
                                                                    let uu____4081
                                                                    =
                                                                    let uu____4082
                                                                    =
                                                                    let uu____4083
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4083 in
                                                                    Prims.op_Negation
                                                                    uu____4082 in
                                                                    if
                                                                    uu____4081
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret () in
                                                                   bind
                                                                    uu____4078
                                                                    (fun
                                                                    uu____4089
                                                                     ->
                                                                    let uu____4090
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals in
                                                                    bind
                                                                    uu____4090
                                                                    (fun
                                                                    uu____4094
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))) in
      focus uu____3012 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3009
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4114 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____4114 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4124::(e1,uu____4126)::(e2,uu____4128)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4187 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4209 = destruct_eq' typ in
    match uu____4209 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4239 = FStar_Syntax_Util.un_squash typ in
        (match uu____4239 with
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
        let uu____4295 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____4295 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4343 = aux e' in
               FStar_Util.map_opt uu____4343
                 (fun uu____4367  ->
                    match uu____4367 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____4388 = aux e in
      FStar_Util.map_opt uu____4388
        (fun uu____4412  ->
           match uu____4412 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____4467 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____4467
            (fun uu____4491  ->
               match uu____4491 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___392_4508 = bv in
                     let uu____4509 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___392_4508.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___392_4508.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4509
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___393_4518 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___393_4518.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___393_4518.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4531 = h in
         match uu____4531 with
         | (bv,uu____4535) ->
             mlog
               (fun uu____4539  ->
                  let uu____4540 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4541 =
                    FStar_Syntax_Print.term_to_string
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4540
                    uu____4541)
               (fun uu____4544  ->
                  let uu____4545 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4545 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4574 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4574 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4589 =
                             let uu____4590 = FStar_Syntax_Subst.compress x in
                             uu____4590.FStar_Syntax_Syntax.n in
                           (match uu____4589 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___394_4603 = bv1 in
                                  let uu____4604 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___394_4603.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___394_4603.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4604
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4610 =
                                  let uu___395_4611 = goal in
                                  let uu____4612 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4613 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4614 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4612;
                                    FStar_Tactics_Types.witness = uu____4613;
                                    FStar_Tactics_Types.goal_ty = uu____4614;
                                    FStar_Tactics_Types.opts =
                                      (uu___395_4611.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___395_4611.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4610
                            | uu____4615 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4616 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4641 = b in
           match uu____4641 with
           | (bv,uu____4645) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___396_4649 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___396_4649.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___396_4649.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4653 =
                   let uu____4654 =
                     let uu____4661 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4661) in
                   FStar_Syntax_Syntax.NT uu____4654 in
                 [uu____4653] in
               let uu____4662 = subst_goal bv bv' s1 goal in
               (match uu____4662 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4681 = b in
         match uu____4681 with
         | (bv,uu____4685) ->
             let uu____4686 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4686 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4715 = FStar_Syntax_Util.type_u () in
                  (match uu____4715 with
                   | (ty,u) ->
                       let uu____4724 = new_uvar "binder_retype" e0 ty in
                       bind uu____4724
                         (fun t'  ->
                            let bv'' =
                              let uu___397_4734 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___397_4734.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___397_4734.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4738 =
                                let uu____4739 =
                                  let uu____4746 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4746) in
                                FStar_Syntax_Syntax.NT uu____4739 in
                              [uu____4738] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___398_4754 = b1 in
                                   let uu____4755 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___398_4754.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___398_4754.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4755
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4761  ->
                                 let uu____4762 =
                                   let uu____4765 =
                                     let uu____4768 =
                                       let uu___399_4769 = goal in
                                       let uu____4770 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4771 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4770;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4771;
                                         FStar_Tactics_Types.opts =
                                           (uu___399_4769.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___399_4769.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4768] in
                                   add_goals uu____4765 in
                                 bind uu____4762
                                   (fun uu____4774  ->
                                      let uu____4775 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4775
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4796 = b in
           match uu____4796 with
           | (bv,uu____4800) ->
               let uu____4801 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4801 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4833 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4833 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___400_4838 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___400_4838.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___400_4838.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___401_4842 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___401_4842.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___401_4842.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___401_4842.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___401_4842.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4848 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4848 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4870 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4870 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___402_4904 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___402_4904.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___402_4904.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4915 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4915 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4936 = FStar_Syntax_Print.bv_to_string x in
               let uu____4937 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4936 uu____4937
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4944 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4944 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4966 = FStar_Util.set_mem x fns_ty in
           if uu____4966
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4970 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4970
                (fun u  ->
                   let uu____4976 =
                     let uu____4977 = trysolve goal u in
                     Prims.op_Negation uu____4977 in
                   if uu____4976
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___403_4982 = goal in
                        let uu____4983 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4983;
                          FStar_Tactics_Types.goal_ty =
                            (uu___403_4982.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___403_4982.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___403_4982.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4985  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4996 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4996 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____5020  ->
                    let uu____5021 = clear b in
                    bind uu____5021
                      (fun uu____5025  ->
                         bind intro (fun uu____5027  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___404_5043 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___404_5043.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___404_5043.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___404_5043.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___404_5043.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5045  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___405_5061 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___405_5061.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___405_5061.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___405_5061.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___405_5061.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____5063  -> add_goals [g']))
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
            let uu____5095 = FStar_Syntax_Subst.compress t in
            uu____5095.FStar_Syntax_Syntax.n in
          let uu____5098 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___407_5104 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___407_5104.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___407_5104.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____5098
            (fun t1  ->
               let tn1 =
                 let uu____5112 =
                   let uu____5113 = FStar_Syntax_Subst.compress t1 in
                   uu____5113.FStar_Syntax_Syntax.n in
                 match uu____5112 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____5145 = ff hd1 in
                     bind uu____5145
                       (fun hd2  ->
                          let fa uu____5165 =
                            match uu____5165 with
                            | (a,q) ->
                                let uu____5178 = ff a in
                                bind uu____5178 (fun a1  -> ret (a1, q)) in
                          let uu____5191 = mapM fa args in
                          bind uu____5191
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5251 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____5251 with
                      | (bs1,t') ->
                          let uu____5260 =
                            let uu____5263 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____5263 t' in
                          bind uu____5260
                            (fun t''  ->
                               let uu____5267 =
                                 let uu____5268 =
                                   let uu____5285 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____5286 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____5285, uu____5286, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____5268 in
                               ret uu____5267))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5307 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___406_5314 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___406_5314.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___406_5314.FStar_Syntax_Syntax.vars)
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
            let uu____5343 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____5343 with
            | (t1,lcomp,g) ->
                let uu____5355 =
                  (let uu____5358 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____5358) ||
                    (let uu____5360 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____5360) in
                if uu____5355
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____5370 = new_uvar "pointwise_rec" env typ in
                     bind uu____5370
                       (fun ut  ->
                          log ps
                            (fun uu____5381  ->
                               let uu____5382 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____5383 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5382 uu____5383);
                          (let uu____5384 =
                             let uu____5387 =
                               let uu____5388 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____5388 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5387 opts in
                           bind uu____5384
                             (fun uu____5391  ->
                                let uu____5392 =
                                  bind tau
                                    (fun uu____5398  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____5404  ->
                                            let uu____5405 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____5406 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5405 uu____5406);
                                       ret ut1) in
                                focus uu____5392))) in
                   let uu____5407 = trytac' rewrite_eq in
                   bind uu____5407
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
           let uu____5449 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5449 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5486  ->
                     let uu____5487 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5487);
                bind dismiss_all
                  (fun uu____5490  ->
                     let uu____5491 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5491
                       (fun gt'  ->
                          log ps
                            (fun uu____5501  ->
                               let uu____5502 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5502);
                          (let uu____5503 = push_goals gs in
                           bind uu____5503
                             (fun uu____5507  ->
                                add_goals
                                  [(let uu___408_5509 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___408_5509.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___408_5509.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___408_5509.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___408_5509.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5529 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5529 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5541 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5541 with
            | (hd1,args) ->
                let uu____5574 =
                  let uu____5587 =
                    let uu____5588 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5588.FStar_Syntax_Syntax.n in
                  (uu____5587, args) in
                (match uu____5574 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5602::(l,uu____5604)::(r,uu____5606)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5653 =
                       let uu____5654 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5654 in
                     if uu____5653
                     then
                       let uu____5657 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____5658 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5657 uu____5658
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5661) ->
                     let uu____5678 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5678))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5686 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5686
         (fun u  ->
            let g' =
              let uu___409_5693 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___409_5693.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___409_5693.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___409_5693.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___409_5693.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5696  ->
                 let uu____5697 =
                   let uu____5700 =
                     let uu____5701 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5701
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5700
                     g.FStar_Tactics_Types.opts in
                 bind uu____5697
                   (fun uu____5704  ->
                      let uu____5705 = add_goals [g'] in
                      bind uu____5705 (fun uu____5709  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___410_5726 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___410_5726.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___410_5726.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___410_5726.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___410_5726.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___410_5726.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___410_5726.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___410_5726.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___410_5726.FStar_Tactics_Types.entry_range)
              })
       | uu____5727 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___411_5742 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___411_5742.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___411_5742.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___411_5742.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___411_5742.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___411_5742.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___411_5742.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___411_5742.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___411_5742.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5749 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5767 =
      bind cur_goal
        (fun g  ->
           let uu____5781 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5781
             (fun uu____5817  ->
                match uu____5817 with
                | (t1,typ,guard) ->
                    let uu____5833 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5833 with
                     | (hd1,args) ->
                         let uu____5876 =
                           let uu____5889 =
                             let uu____5890 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5890.FStar_Syntax_Syntax.n in
                           (uu____5889, args) in
                         (match uu____5876 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5909)::(q,uu____5911)::[]) when
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
                                let uu___412_5949 = g in
                                let uu____5950 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5950;
                                  FStar_Tactics_Types.witness =
                                    (uu___412_5949.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___412_5949.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___412_5949.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___412_5949.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___413_5952 = g in
                                let uu____5953 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5953;
                                  FStar_Tactics_Types.witness =
                                    (uu___413_5952.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___413_5952.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___413_5952.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___413_5952.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5960  ->
                                   let uu____5961 = add_goals [g1; g2] in
                                   bind uu____5961
                                     (fun uu____5970  ->
                                        let uu____5971 =
                                          let uu____5976 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5977 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5976, uu____5977) in
                                        ret uu____5971))
                          | uu____5982 ->
                              let uu____5995 =
                                FStar_TypeChecker_Normalize.term_to_string
                                  g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5995)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5767
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6033 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____6033);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___414_6040 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___414_6040.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___414_6040.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___414_6040.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___414_6040.FStar_Tactics_Types.is_guard)
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
      let uu____6076 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____6084 = __tc env tm in
             bind uu____6084
               (fun uu____6104  ->
                  match uu____6104 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____6076
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____6135 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6141 =
              let uu____6142 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6142 in
            new_uvar "uvar_env.2" env uu____6141 in
      bind uu____6135
        (fun typ  ->
           let uu____6154 = new_uvar "uvar_env" env typ in
           bind uu____6154 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____6166 =
      bind cur_goal
        (fun goal  ->
           let uu____6172 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____6172
             (fun uu____6192  ->
                match uu____6192 with
                | (t1,typ,guard) ->
                    let uu____6204 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____6204
                      (fun uu____6209  ->
                         let uu____6210 =
                           let uu____6213 =
                             let uu___415_6214 = goal in
                             let uu____6215 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____6216 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___415_6214.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6215;
                               FStar_Tactics_Types.goal_ty = uu____6216;
                               FStar_Tactics_Types.opts =
                                 (uu___415_6214.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____6213] in
                         add_goals uu____6210))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6166
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6234 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____6234)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6251  ->
             let uu____6252 = FStar_Options.unsafe_tactic_exec () in
             if uu____6252
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6258  -> fun uu____6259  -> false) in
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
      let uu____6279 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____6279 with
      | (u,uu____6297,g_u) ->
          let g =
            let uu____6312 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6312;
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
      let uu____6327 = goal_of_goal_ty env typ in
      match uu____6327 with
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