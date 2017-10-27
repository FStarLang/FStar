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
         let uu___356_909 = p in
         let uu____910 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___356_909.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___356_909.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___356_909.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____910;
           FStar_Tactics_Types.smt_goals =
             (uu___356_909.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___356_909.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___356_909.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___356_909.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___356_909.FStar_Tactics_Types.entry_range)
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
         (let uu___357_937 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___357_937.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___357_937.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___357_937.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___357_937.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___357_937.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___357_937.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___357_937.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___357_937.FStar_Tactics_Types.entry_range)
          }))
let check_valid_goal: FStar_Tactics_Types.goal -> Prims.unit =
  fun g  ->
    let b = true in
    let env = g.FStar_Tactics_Types.context in
    let b1 =
      b && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.witness) in
    let b2 =
      b1 && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.goal_ty) in
    let rec aux b3 e =
      let uu____952 = FStar_TypeChecker_Env.pop_bv e in
      match uu____952 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____970 = let uu____971 = aux b2 env in Prims.op_Negation uu____971 in
    if uu____970
    then
      let uu____972 =
        let uu____973 = goal_to_string g in
        FStar_Util.format1
          "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
          uu____973 in
      FStar_Errors.warn
        (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____972
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___358_992 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___358_992.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___358_992.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___358_992.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___358_992.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___358_992.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___358_992.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___358_992.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___358_992.FStar_Tactics_Types.entry_range)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___359_1010 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___359_1010.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___359_1010.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___359_1010.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___359_1010.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___359_1010.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___359_1010.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___359_1010.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___359_1010.FStar_Tactics_Types.entry_range)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___360_1028 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___360_1028.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___360_1028.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___360_1028.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___360_1028.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___360_1028.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___360_1028.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___360_1028.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___360_1028.FStar_Tactics_Types.entry_range)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___361_1046 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___361_1046.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___361_1046.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___361_1046.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___361_1046.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___361_1046.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___361_1046.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___361_1046.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___361_1046.FStar_Tactics_Types.entry_range)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1055  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___362_1067 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___362_1067.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___362_1067.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___362_1067.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___362_1067.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___362_1067.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___362_1067.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___362_1067.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___362_1067.FStar_Tactics_Types.entry_range)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1093 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1093 with
        | (u,uu____1109,g_u) ->
            let uu____1123 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1123 (fun uu____1127  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1131 = FStar_Syntax_Util.un_squash t in
    match uu____1131 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1141 =
          let uu____1142 = FStar_Syntax_Subst.compress t' in
          uu____1142.FStar_Syntax_Syntax.n in
        (match uu____1141 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1146 -> false)
    | uu____1147 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1155 = FStar_Syntax_Util.un_squash t in
    match uu____1155 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1165 =
          let uu____1166 = FStar_Syntax_Subst.compress t' in
          uu____1166.FStar_Syntax_Syntax.n in
        (match uu____1165 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1170 -> false)
    | uu____1171 -> false
let cur_goal: FStar_Tactics_Types.goal tac =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
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
          let uu____1205 = new_uvar reason env typ in
          bind uu____1205
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
             let uu____1261 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1261
           with | e1 -> fail "not typeable")
let must_trivial: env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1309 =
          let uu____1310 =
            let uu____1311 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1311 in
          Prims.op_Negation uu____1310 in
        if uu____1309 then fail "got non-trivial guard" else ret ()
      with | uu____1320 -> fail "got non-trivial guard"
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1328 =
      bind cur_goal
        (fun goal  ->
           let uu____1334 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1334
             (fun uu____1354  ->
                match uu____1354 with
                | (t1,typ,guard) ->
                    let uu____1366 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____1366 (fun uu____1370  -> ret typ))) in
    FStar_All.pipe_left (wrap_err "tc") uu____1328
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1391 = mk_irrelevant_goal reason env phi opts in
          bind uu____1391 (fun goal  -> add_goals [goal])
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
       let uu____1411 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1411
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1415 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1415))
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
          let uu____1432 =
            let uu____1433 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1433.FStar_TypeChecker_Env.guard_f in
          match uu____1432 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1437 = istrivial e f in
              if uu____1437
              then ret ()
              else
                (let uu____1441 = mk_irrelevant_goal reason e f opts in
                 bind uu____1441
                   (fun goal  ->
                      let goal1 =
                        let uu___367_1448 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___367_1448.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___367_1448.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___367_1448.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___367_1448.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard = true
                        } in
                      push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1454 = is_irrelevant g in
       if uu____1454
       then bind dismiss (fun uu____1458  -> add_smt_goals [g])
       else
         (let uu____1460 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1460))
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
             let uu____1501 =
               try
                 let uu____1535 =
                   let uu____1544 = FStar_BigInt.to_int_fs n1 in
                   FStar_List.splitAt uu____1544 p.FStar_Tactics_Types.goals in
                 ret uu____1535
               with | uu____1566 -> fail "divide: not enough goals" in
             bind uu____1501
               (fun uu____1593  ->
                  match uu____1593 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___368_1619 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___368_1619.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___368_1619.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___368_1619.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___368_1619.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___368_1619.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___368_1619.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___368_1619.FStar_Tactics_Types.entry_range)
                        } in
                      let rp =
                        let uu___369_1621 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___369_1621.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___369_1621.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___369_1621.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___369_1621.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___369_1621.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___369_1621.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___369_1621.FStar_Tactics_Types.entry_range)
                        } in
                      let uu____1622 = set lp in
                      bind uu____1622
                        (fun uu____1630  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1644 = set rp in
                                     bind uu____1644
                                       (fun uu____1652  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___370_1668 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___370_1668.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___370_1668.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___370_1668.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___370_1668.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___370_1668.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___370_1668.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___370_1668.FStar_Tactics_Types.entry_range)
                                                      } in
                                                    let uu____1669 = set p' in
                                                    bind uu____1669
                                                      (fun uu____1677  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1695 = divide FStar_BigInt.one f idtac in
    bind uu____1695
      (fun uu____1708  -> match uu____1708 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1741::uu____1742 ->
             let uu____1745 =
               let uu____1754 = map tau in
               divide FStar_BigInt.one tau uu____1754 in
             bind uu____1745
               (fun uu____1772  ->
                  match uu____1772 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1809 =
        bind t1
          (fun uu____1814  ->
             let uu____1815 = map t2 in
             bind uu____1815 (fun uu____1823  -> ret ())) in
      focus uu____1809
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1834 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1834 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1849 =
             let uu____1850 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1850 in
           if uu____1849
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1856 = new_uvar "intro" env' typ' in
              bind uu____1856
                (fun u  ->
                   let uu____1863 =
                     let uu____1864 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1864 in
                   if uu____1863
                   then
                     let uu____1867 =
                       let uu____1870 =
                         let uu___373_1871 = goal in
                         let uu____1872 = bnorm env' u in
                         let uu____1873 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1872;
                           FStar_Tactics_Types.goal_ty = uu____1873;
                           FStar_Tactics_Types.opts =
                             (uu___373_1871.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___373_1871.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1870 in
                     bind uu____1867 (fun uu____1875  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1881 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1881)
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
       (let uu____1902 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1902 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1921 =
              let uu____1922 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1922 in
            if uu____1921
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1938 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1938; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1940 =
                 let uu____1943 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____1943 in
               bind uu____1940
                 (fun u  ->
                    let lb =
                      let uu____1959 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____1959 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1963 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1963 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2000 =
                            let uu____2003 =
                              let uu___374_2004 = goal in
                              let uu____2005 = bnorm env' u in
                              let uu____2006 =
                                let uu____2007 = comp_to_typ c in
                                bnorm env' uu____2007 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2005;
                                FStar_Tactics_Types.goal_ty = uu____2006;
                                FStar_Tactics_Types.opts =
                                  (uu___374_2004.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___374_2004.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2003 in
                          bind uu____2000
                            (fun uu____2014  ->
                               let uu____2015 =
                                 let uu____2020 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2020, b) in
                               ret uu____2015)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2034 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2034))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2058 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2058 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___375_2065 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___375_2065.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___375_2065.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___375_2065.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2083 =
          bind get
            (fun ps  ->
               let uu____2089 = __tc e t in
               bind uu____2089
                 (fun uu____2111  ->
                    match uu____2111 with
                    | (t1,uu____2121,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2127 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2127 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2083
let __exact: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun force_guard  ->
    fun t  ->
      bind cur_goal
        (fun goal  ->
           let uu____2148 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____2148
             (fun uu____2168  ->
                match uu____2168 with
                | (t1,typ,guard) ->
                    let uu____2180 =
                      if force_guard
                      then
                        must_trivial goal.FStar_Tactics_Types.context guard
                      else
                        add_goal_from_guard "__exact typing"
                          goal.FStar_Tactics_Types.context guard
                          goal.FStar_Tactics_Types.opts in
                    bind uu____2180
                      (fun uu____2188  ->
                         let uu____2189 =
                           do_unify goal.FStar_Tactics_Types.context typ
                             goal.FStar_Tactics_Types.goal_ty in
                         if uu____2189
                         then solve goal t1
                         else
                           (let uu____2193 =
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context t1 in
                            let uu____2194 =
                              let uu____2195 =
                                bnorm goal.FStar_Tactics_Types.context typ in
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context uu____2195 in
                            let uu____2196 =
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context
                                goal.FStar_Tactics_Types.goal_ty in
                            fail3
                              "%s : %s does not exactly solve the goal %s"
                              uu____2193 uu____2194 uu____2196))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2204 =
      mlog
        (fun uu____2209  ->
           let uu____2210 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact: tm = %s\n" uu____2210)
        (fun uu____2213  ->
           let uu____2214 = __exact true tm in focus uu____2214) in
    FStar_All.pipe_left (wrap_err "exact") uu____2204
let exact_guard: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2228 =
      mlog
        (fun uu____2233  ->
           let uu____2234 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact_guard: tm = %s\n" uu____2234)
        (fun uu____2237  ->
           let uu____2238 = __exact false tm in focus uu____2238) in
    FStar_All.pipe_left (wrap_err "exact_guard") uu____2228
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2255 =
             let uu____2262 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2262 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2255 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2286 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2303 =
               let uu____2308 = __exact true tm in trytac uu____2308 in
             bind uu____2303
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2321 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2321 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2353  ->
                                let uu____2354 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2354)
                             (fun uu____2357  ->
                                let uu____2358 =
                                  let uu____2359 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2359 in
                                if uu____2358
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2363 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2363
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2383 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2383 in
                                        let uu____2384 =
                                          __apply uopt tm' typ' in
                                        bind uu____2384
                                          (fun uu____2392  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2394 =
                                               let uu____2395 =
                                                 let uu____2398 =
                                                   let uu____2399 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2399 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2398 in
                                               uu____2395.FStar_Syntax_Syntax.n in
                                             match uu____2394 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2427) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2455 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2455
                                                      then ret ()
                                                      else
                                                        (let uu____2459 =
                                                           let uu____2462 =
                                                             let uu___376_2463
                                                               = goal in
                                                             let uu____2464 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2465 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___376_2463.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2464;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2465;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___376_2463.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2462] in
                                                         add_goals uu____2459))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2511 =
        mlog
          (fun uu____2516  ->
             let uu____2517 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2517)
          (fun uu____2519  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2523 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2523
                    (fun uu____2544  ->
                       match uu____2544 with
                       | (tm1,typ,guard) ->
                           let uu____2556 =
                             let uu____2559 =
                               let uu____2562 = __apply uopt tm1 typ in
                               bind uu____2562
                                 (fun uu____2566  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2559 in
                           let uu____2567 =
                             let uu____2570 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context tm1 in
                             let uu____2571 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context typ in
                             let uu____2572 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2570 uu____2571 uu____2572 in
                           try_unif uu____2556 uu____2567))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2511
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2584 =
      let uu____2587 =
        mlog
          (fun uu____2592  ->
             let uu____2593 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2593)
          (fun uu____2596  ->
             let is_unit_t t =
               let uu____2601 =
                 let uu____2602 = FStar_Syntax_Subst.compress t in
                 uu____2602.FStar_Syntax_Syntax.n in
               match uu____2601 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____2606 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____2610 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2610
                    (fun uu____2632  ->
                       match uu____2632 with
                       | (tm1,t,guard) ->
                           let uu____2644 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____2644 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____2674 =
                                     FStar_List.fold_left
                                       (fun uu____2720  ->
                                          fun uu____2721  ->
                                            match (uu____2720, uu____2721)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____2824 =
                                                  is_unit_t b_t in
                                                if uu____2824
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____2862 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____2862 with
                                                   | (u,uu____2892,g_u) ->
                                                       let uu____2906 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____2906,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____2674 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____2976 =
                                         let uu____2985 =
                                           let uu____2994 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____2994.FStar_Syntax_Syntax.effect_args in
                                         match uu____2985 with
                                         | pre::post::uu____3005 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3046 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____2976 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3078 =
                                                let uu____3087 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3087] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3078 in
                                            let uu____3088 =
                                              let uu____3089 =
                                                let uu____3090 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3090
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3089 in
                                            if uu____3088
                                            then
                                              let uu____3093 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3094 =
                                                let uu____3095 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3095 in
                                              let uu____3096 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3093 uu____3094
                                                uu____3096
                                            else
                                              (let solution =
                                                 let uu____3099 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3099 in
                                               let uu____3100 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3100
                                                 (fun uu____3106  ->
                                                    let implicits1 =
                                                      FStar_All.pipe_right
                                                        implicits.FStar_TypeChecker_Env.implicits
                                                        (FStar_List.filter
                                                           (fun uu____3174 
                                                              ->
                                                              match uu____3174
                                                              with
                                                              | (uu____3187,uu____3188,uu____3189,tm2,uu____3191,uu____3192)
                                                                  ->
                                                                  let uu____3193
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    tm2 in
                                                                  (match uu____3193
                                                                   with
                                                                   | 
                                                                   (hd1,uu____3209)
                                                                    ->
                                                                    let uu____3230
                                                                    =
                                                                    let uu____3231
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3231.FStar_Syntax_Syntax.n in
                                                                    (match uu____3230
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3234
                                                                    -> true
                                                                    | 
                                                                    uu____3251
                                                                    -> false)))) in
                                                    let uu____3252 =
                                                      solve goal solution in
                                                    bind uu____3252
                                                      (fun uu____3263  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3274 =
                                                               let uu____3281
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3281 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3274 in
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
                                                           let uu____3322 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3322
                                                           with
                                                           | (hd1,uu____3338)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3360)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3385
                                                                    -> false) in
                                                         let sub_goals =
                                                           FStar_All.pipe_right
                                                             implicits1
                                                             (FStar_List.map
                                                                (fun
                                                                   uu____3427
                                                                    ->
                                                                   match uu____3427
                                                                   with
                                                                   | 
                                                                   (_msg,_env,_uvar,term,typ,uu____3445)
                                                                    ->
                                                                    let uu___379_3446
                                                                    = goal in
                                                                    let uu____3447
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3448
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___379_3446.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3447;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3448;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___379_3446.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___379_3446.FStar_Tactics_Types.is_guard)
                                                                    })) in
                                                         let rec filter' f xs
                                                           =
                                                           match xs with
                                                           | [] -> []
                                                           | x::xs1 ->
                                                               let uu____3486
                                                                 = f x xs1 in
                                                               if uu____3486
                                                               then
                                                                 let uu____3489
                                                                   =
                                                                   filter' f
                                                                    xs1 in
                                                                 x ::
                                                                   uu____3489
                                                               else
                                                                 filter' f
                                                                   xs1 in
                                                         let sub_goals1 =
                                                           filter'
                                                             (fun g  ->
                                                                fun goals  ->
                                                                  let uu____3503
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                  Prims.op_Negation
                                                                    uu____3503)
                                                             sub_goals in
                                                         let uu____3504 =
                                                           add_goal_from_guard
                                                             "apply_lemma guard"
                                                             goal.FStar_Tactics_Types.context
                                                             guard
                                                             goal.FStar_Tactics_Types.opts in
                                                         bind uu____3504
                                                           (fun uu____3509 
                                                              ->
                                                              let uu____3510
                                                                =
                                                                let uu____3513
                                                                  =
                                                                  let uu____3514
                                                                    =
                                                                    let uu____3515
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____3515 in
                                                                  Prims.op_Negation
                                                                    uu____3514 in
                                                                if uu____3513
                                                                then
                                                                  add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                else ret () in
                                                              bind uu____3510
                                                                (fun
                                                                   uu____3520
                                                                    ->
                                                                   add_goals
                                                                    sub_goals1))))))))))) in
      focus uu____2587 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2584
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3540 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3540 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3550::(e1,uu____3552)::(e2,uu____3554)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3613 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3635 = destruct_eq' typ in
    match uu____3635 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3665 = FStar_Syntax_Util.un_squash typ in
        (match uu____3665 with
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
        let uu____3721 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3721 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3769 = aux e' in
               FStar_Util.map_opt uu____3769
                 (fun uu____3793  ->
                    match uu____3793 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3814 = aux e in
      FStar_Util.map_opt uu____3814
        (fun uu____3838  ->
           match uu____3838 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____3893 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____3893
            (fun uu____3917  ->
               match uu____3917 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___380_3934 = bv in
                     let uu____3935 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___380_3934.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___380_3934.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3935
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___381_3944 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___381_3944.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___381_3944.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3957 = h in
         match uu____3957 with
         | (bv,uu____3961) ->
             mlog
               (fun uu____3965  ->
                  let uu____3966 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____3967 =
                    FStar_Syntax_Print.term_to_string
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3966
                    uu____3967)
               (fun uu____3970  ->
                  let uu____3971 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____3971 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4000 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4000 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4015 =
                             let uu____4016 = FStar_Syntax_Subst.compress x in
                             uu____4016.FStar_Syntax_Syntax.n in
                           (match uu____4015 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___382_4029 = bv1 in
                                  let uu____4030 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___382_4029.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___382_4029.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4030
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4036 =
                                  let uu___383_4037 = goal in
                                  let uu____4038 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4039 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4040 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4038;
                                    FStar_Tactics_Types.witness = uu____4039;
                                    FStar_Tactics_Types.goal_ty = uu____4040;
                                    FStar_Tactics_Types.opts =
                                      (uu___383_4037.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___383_4037.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4036
                            | uu____4041 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4042 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4067 = b in
           match uu____4067 with
           | (bv,uu____4071) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___384_4075 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___384_4075.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___384_4075.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4079 =
                   let uu____4080 =
                     let uu____4087 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4087) in
                   FStar_Syntax_Syntax.NT uu____4080 in
                 [uu____4079] in
               let uu____4088 = subst_goal bv bv' s1 goal in
               (match uu____4088 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4107 = b in
         match uu____4107 with
         | (bv,uu____4111) ->
             let uu____4112 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4112 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4141 = FStar_Syntax_Util.type_u () in
                  (match uu____4141 with
                   | (ty,u) ->
                       let uu____4150 = new_uvar "binder_retype" e0 ty in
                       bind uu____4150
                         (fun t'  ->
                            let bv'' =
                              let uu___385_4160 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___385_4160.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___385_4160.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4164 =
                                let uu____4165 =
                                  let uu____4172 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4172) in
                                FStar_Syntax_Syntax.NT uu____4165 in
                              [uu____4164] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___386_4180 = b1 in
                                   let uu____4181 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___386_4180.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___386_4180.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4181
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4187  ->
                                 let uu____4188 =
                                   let uu____4191 =
                                     let uu____4194 =
                                       let uu___387_4195 = goal in
                                       let uu____4196 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4197 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4196;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4197;
                                         FStar_Tactics_Types.opts =
                                           (uu___387_4195.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___387_4195.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4194] in
                                   add_goals uu____4191 in
                                 bind uu____4188
                                   (fun uu____4200  ->
                                      let uu____4201 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4201
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4222 = b in
           match uu____4222 with
           | (bv,uu____4226) ->
               let uu____4227 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4227 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4259 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4259 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___388_4264 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___388_4264.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___388_4264.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___389_4268 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___389_4268.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___389_4268.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___389_4268.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___389_4268.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4274 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4274 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4296 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4296 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___390_4330 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___390_4330.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___390_4330.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4341 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4341 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4362 = FStar_Syntax_Print.bv_to_string x in
               let uu____4363 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4362 uu____4363
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4370 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4370 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4392 = FStar_Util.set_mem x fns_ty in
           if uu____4392
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4396 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4396
                (fun u  ->
                   let uu____4402 =
                     let uu____4403 = trysolve goal u in
                     Prims.op_Negation uu____4403 in
                   if uu____4402
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___391_4408 = goal in
                        let uu____4409 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4409;
                          FStar_Tactics_Types.goal_ty =
                            (uu___391_4408.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___391_4408.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___391_4408.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4411  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4422 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4422 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4446  ->
                    let uu____4447 = clear b in
                    bind uu____4447
                      (fun uu____4451  ->
                         bind intro (fun uu____4453  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___392_4469 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___392_4469.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___392_4469.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___392_4469.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___392_4469.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4471  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___393_4487 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___393_4487.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___393_4487.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___393_4487.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___393_4487.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4489  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4527 = f x in
          bind uu____4527
            (fun y  ->
               let uu____4535 = mapM f xs in
               bind uu____4535 (fun ys  -> ret (y :: ys)))
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
            let uu____4581 = FStar_Syntax_Subst.compress t in
            uu____4581.FStar_Syntax_Syntax.n in
          let uu____4584 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___395_4590 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___395_4590.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___395_4590.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____4584
            (fun t1  ->
               let tn1 =
                 let uu____4598 =
                   let uu____4599 = FStar_Syntax_Subst.compress t1 in
                   uu____4599.FStar_Syntax_Syntax.n in
                 match uu____4598 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____4631 = ff hd1 in
                     bind uu____4631
                       (fun hd2  ->
                          let fa uu____4651 =
                            match uu____4651 with
                            | (a,q) ->
                                let uu____4664 = ff a in
                                bind uu____4664 (fun a1  -> ret (a1, q)) in
                          let uu____4677 = mapM fa args in
                          bind uu____4677
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____4737 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____4737 with
                      | (bs1,t') ->
                          let uu____4746 =
                            let uu____4749 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____4749 t' in
                          bind uu____4746
                            (fun t''  ->
                               let uu____4753 =
                                 let uu____4754 =
                                   let uu____4771 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____4772 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____4771, uu____4772, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____4754 in
                               ret uu____4753))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____4793 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___394_4800 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___394_4800.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___394_4800.FStar_Syntax_Syntax.vars)
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
            let uu____4829 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4829 with
            | (t1,lcomp,g) ->
                let uu____4841 =
                  (let uu____4844 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____4844) ||
                    (let uu____4846 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4846) in
                if uu____4841
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____4856 = new_uvar "pointwise_rec" env typ in
                     bind uu____4856
                       (fun ut  ->
                          log ps
                            (fun uu____4867  ->
                               let uu____4868 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____4869 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____4868 uu____4869);
                          (let uu____4870 =
                             let uu____4873 =
                               let uu____4874 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____4874 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____4873 opts in
                           bind uu____4870
                             (fun uu____4877  ->
                                let uu____4878 =
                                  bind tau
                                    (fun uu____4884  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____4890  ->
                                            let uu____4891 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____4892 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____4891 uu____4892);
                                       ret ut1) in
                                focus uu____4878))) in
                   let uu____4893 = trytac' rewrite_eq in
                   bind uu____4893
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
           let uu____4935 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____4935 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____4972  ->
                     let uu____4973 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____4973);
                bind dismiss_all
                  (fun uu____4976  ->
                     let uu____4977 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____4977
                       (fun gt'  ->
                          log ps
                            (fun uu____4987  ->
                               let uu____4988 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____4988);
                          (let uu____4989 = push_goals gs in
                           bind uu____4989
                             (fun uu____4993  ->
                                add_goals
                                  [(let uu___396_4995 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___396_4995.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___396_4995.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___396_4995.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___396_4995.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5015 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5015 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5027 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5027 with
            | (hd1,args) ->
                let uu____5060 =
                  let uu____5073 =
                    let uu____5074 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5074.FStar_Syntax_Syntax.n in
                  (uu____5073, args) in
                (match uu____5060 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5088::(l,uu____5090)::(r,uu____5092)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5139 =
                       let uu____5140 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5140 in
                     if uu____5139
                     then
                       let uu____5143 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____5144 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5143 uu____5144
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5147) ->
                     let uu____5164 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5164))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5172 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5172
         (fun u  ->
            let g' =
              let uu___397_5179 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___397_5179.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___397_5179.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___397_5179.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___397_5179.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5182  ->
                 let uu____5183 =
                   let uu____5186 =
                     let uu____5187 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5187
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5186
                     g.FStar_Tactics_Types.opts in
                 bind uu____5183
                   (fun uu____5190  ->
                      let uu____5191 = add_goals [g'] in
                      bind uu____5191 (fun uu____5195  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___398_5212 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___398_5212.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___398_5212.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___398_5212.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___398_5212.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___398_5212.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___398_5212.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___398_5212.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___398_5212.FStar_Tactics_Types.entry_range)
              })
       | uu____5213 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___399_5228 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___399_5228.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___399_5228.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___399_5228.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___399_5228.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___399_5228.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___399_5228.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___399_5228.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___399_5228.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5235 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5253 =
      bind cur_goal
        (fun g  ->
           let uu____5267 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5267
             (fun uu____5303  ->
                match uu____5303 with
                | (t1,typ,guard) ->
                    let uu____5319 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5319 with
                     | (hd1,args) ->
                         let uu____5362 =
                           let uu____5375 =
                             let uu____5376 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5376.FStar_Syntax_Syntax.n in
                           (uu____5375, args) in
                         (match uu____5362 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5395)::(q,uu____5397)::[]) when
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
                                let uu___400_5435 = g in
                                let uu____5436 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5436;
                                  FStar_Tactics_Types.witness =
                                    (uu___400_5435.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___400_5435.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___400_5435.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___400_5435.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___401_5438 = g in
                                let uu____5439 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5439;
                                  FStar_Tactics_Types.witness =
                                    (uu___401_5438.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___401_5438.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___401_5438.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___401_5438.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5446  ->
                                   let uu____5447 = add_goals [g1; g2] in
                                   bind uu____5447
                                     (fun uu____5456  ->
                                        let uu____5457 =
                                          let uu____5462 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5463 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5462, uu____5463) in
                                        ret uu____5457))
                          | uu____5468 ->
                              let uu____5481 =
                                FStar_TypeChecker_Normalize.term_to_string
                                  g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5481)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5253
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5519 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5519);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___402_5526 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___402_5526.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___402_5526.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___402_5526.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___402_5526.FStar_Tactics_Types.is_guard)
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
      let uu____5562 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____5570 = __tc env tm in
             bind uu____5570
               (fun uu____5590  ->
                  match uu____5590 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____5562
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5621 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5627 =
              let uu____5628 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5628 in
            new_uvar "uvar_env.2" env uu____5627 in
      bind uu____5621
        (fun typ  ->
           let uu____5640 = new_uvar "uvar_env" env typ in
           bind uu____5640 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____5652 =
      bind cur_goal
        (fun goal  ->
           let uu____5658 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____5658
             (fun uu____5678  ->
                match uu____5678 with
                | (t1,typ,guard) ->
                    let uu____5690 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____5690
                      (fun uu____5695  ->
                         let uu____5696 =
                           let uu____5699 =
                             let uu___403_5700 = goal in
                             let uu____5701 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____5702 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___403_5700.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____5701;
                               FStar_Tactics_Types.goal_ty = uu____5702;
                               FStar_Tactics_Types.opts =
                                 (uu___403_5700.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____5699] in
                         add_goals uu____5696))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____5652
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5720 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5720)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5737  ->
             let uu____5738 = FStar_Options.unsafe_tactic_exec () in
             if uu____5738
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5744  -> fun uu____5745  -> false) in
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
      let uu____5765 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5765 with
      | (u,uu____5783,g_u) ->
          let g =
            let uu____5798 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5798;
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
      let uu____5813 = goal_of_goal_ty env typ in
      match uu____5813 with
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