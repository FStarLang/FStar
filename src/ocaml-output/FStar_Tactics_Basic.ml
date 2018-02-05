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
  = fun t  -> fun p  -> let r = t.tac_f p in r
let ret: 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p))
let bind: 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____143 = run t1 p in
           match uu____143 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____150 = t2 a in run uu____150 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: FStar_Tactics_Types.goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____161 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____161
        (FStar_Syntax_Print.binders_to_string ", ") in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
    let uu____164 = tts g.FStar_Tactics_Types.context w in
    let uu____165 = tts g.FStar_Tactics_Types.context t in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____164 uu____165
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____175 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____175
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____185 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____185
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____198 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____198
let comp_to_typ: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____203) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____213) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: FStar_Tactics_Types.goal -> Prims.bool =
  fun g  ->
    let uu____226 =
      let uu____231 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty in
      FStar_Syntax_Util.un_squash uu____231 in
    match uu____226 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____237 -> false
let dump_goal:
  'Auu____245 . 'Auu____245 -> FStar_Tactics_Types.goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____255 = goal_to_string goal in tacprint uu____255
let dump_cur: FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____263 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____267 = FStar_List.hd ps.FStar_Tactics_Types.goals in
            dump_goal ps uu____267))
let ps_to_string:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu____274  ->
    match uu____274 with
    | (msg,ps) ->
        let uu____281 =
          let uu____284 =
            let uu____285 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____285 msg in
          let uu____286 =
            let uu____289 =
              let uu____290 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range in
              FStar_Util.format1 "Position: %s\n" uu____290 in
            let uu____291 =
              let uu____294 =
                let uu____295 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals) in
                let uu____296 =
                  let uu____297 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals in
                  FStar_String.concat "\n" uu____297 in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____295
                  uu____296 in
              let uu____300 =
                let uu____303 =
                  let uu____304 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals) in
                  let uu____305 =
                    let uu____306 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals in
                    FStar_String.concat "\n" uu____306 in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____304
                    uu____305 in
                [uu____303] in
              uu____294 :: uu____300 in
            uu____289 :: uu____291 in
          uu____284 :: uu____286 in
        FStar_String.concat "" uu____281
let goal_to_json: FStar_Tactics_Types.goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____313 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____313 FStar_Syntax_Print.binders_to_json in
    let uu____314 =
      let uu____321 =
        let uu____328 =
          let uu____333 =
            let uu____334 =
              let uu____341 =
                let uu____346 =
                  let uu____347 =
                    tts g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness in
                  FStar_Util.JsonStr uu____347 in
                ("witness", uu____346) in
              let uu____348 =
                let uu____355 =
                  let uu____360 =
                    let uu____361 =
                      tts g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty in
                    FStar_Util.JsonStr uu____361 in
                  ("type", uu____360) in
                [uu____355] in
              uu____341 :: uu____348 in
            FStar_Util.JsonAssoc uu____334 in
          ("goal", uu____333) in
        [uu____328] in
      ("hyps", g_binders) :: uu____321 in
    FStar_Util.JsonAssoc uu____314
let ps_to_json:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____392  ->
    match uu____392 with
    | (msg,ps) ->
        let uu____399 =
          let uu____406 =
            let uu____413 =
              let uu____418 =
                let uu____419 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals in
                FStar_Util.JsonList uu____419 in
              ("goals", uu____418) in
            let uu____422 =
              let uu____429 =
                let uu____434 =
                  let uu____435 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals in
                  FStar_Util.JsonList uu____435 in
                ("smt-goals", uu____434) in
              [uu____429] in
            uu____413 :: uu____422 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____406 in
        FStar_Util.JsonAssoc uu____399
let dump_proofstate:
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____462  ->
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
         (let uu____483 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_cur uu____483 msg);
         FStar_Tactics_Result.Success ((), ps))
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc in
         (let uu____499 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_proofstate uu____499 msg);
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
      let uu____532 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____532 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____559 =
              let uu____562 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____562 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____559);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'Auu____620 . Prims.string -> 'Auu____620 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____631 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____631
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____636 . Prims.string -> Prims.string -> 'Auu____636 tac =
  fun msg  ->
    fun x  -> let uu____647 = FStar_Util.format1 msg x in fail uu____647
let fail2:
  'Auu____652 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____652 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____667 = FStar_Util.format2 msg x y in fail uu____667
let fail3:
  'Auu____673 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____673 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____692 = FStar_Util.format3 msg x y z in fail uu____692
let trytac': 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____722 = run t ps in
         match uu____722 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____743) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____768 = trytac' t in
    bind uu____768
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____795 -> ret FStar_Pervasives_Native.None)
let wrap_err: 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____821 = run t ps in
           match uu____821 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____838  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____851 =
          let uu____852 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck" in
          () in
        let debug_off uu____856 =
          let uu____857 = FStar_Options.set_options FStar_Options.Reset "" in
          () in
        (let uu____859 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346") in
         if uu____859
         then
           (debug_on ();
            (let uu____861 = FStar_Syntax_Print.term_to_string t1 in
             let uu____862 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____861
               uu____862))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2 in
           debug_off (); res
         with | uu____874 -> (debug_off (); false))
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____887 =
         let uu___62_888 = p in
         let uu____889 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___62_888.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___62_888.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___62_888.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____889;
           FStar_Tactics_Types.smt_goals =
             (uu___62_888.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___62_888.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___62_888.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___62_888.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___62_888.FStar_Tactics_Types.entry_range)
         } in
       set uu____887)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____902 = trysolve goal solution in
      if uu____902
      then dismiss
      else
        (let uu____906 =
           let uu____907 = tts goal.FStar_Tactics_Types.context solution in
           let uu____908 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____909 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____907 uu____908
             uu____909 in
         fail uu____906)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___63_916 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___63_916.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___63_916.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___63_916.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___63_916.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___63_916.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___63_916.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___63_916.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___63_916.FStar_Tactics_Types.entry_range)
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
      let uu____944 = FStar_TypeChecker_Env.pop_bv e in
      match uu____944 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____962 =
      (let uu____965 = aux b2 env in Prims.op_Negation uu____965) &&
        (let uu____967 = FStar_ST.op_Bang nwarn in
         uu____967 < (Prims.parse_int "5")) in
    if uu____962
    then
      ((let uu____988 =
          let uu____993 =
            let uu____994 = goal_to_string g in
            FStar_Util.format1
              "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
              uu____994 in
          (FStar_Errors.Warning_IllFormedGoal, uu____993) in
        FStar_Errors.log_issue
          (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____988);
       (let uu____995 =
          let uu____996 = FStar_ST.op_Bang nwarn in
          uu____996 + (Prims.parse_int "1") in
        FStar_ST.op_Colon_Equals nwarn uu____995))
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___64_1053 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___64_1053.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___64_1053.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___64_1053.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___64_1053.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___64_1053.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___64_1053.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___64_1053.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___64_1053.FStar_Tactics_Types.entry_range)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1071 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1071.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1071.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1071.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___65_1071.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1071.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1071.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1071.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1071.FStar_Tactics_Types.entry_range)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1089 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1089.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1089.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1089.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___66_1089.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___66_1089.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1089.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1089.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1089.FStar_Tactics_Types.entry_range)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___67_1107 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1107.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1107.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___67_1107.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___67_1107.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___67_1107.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1107.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1107.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1107.FStar_Tactics_Types.entry_range)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1116  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___68_1128 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___68_1128.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___68_1128.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___68_1128.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___68_1128.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___68_1128.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___68_1128.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___68_1128.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___68_1128.FStar_Tactics_Types.entry_range)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1154 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1154 with
        | (u,uu____1170,g_u) ->
            let uu____1184 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1184 (fun uu____1188  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1192 = FStar_Syntax_Util.un_squash t in
    match uu____1192 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1202 =
          let uu____1203 = FStar_Syntax_Subst.compress t' in
          uu____1203.FStar_Syntax_Syntax.n in
        (match uu____1202 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1207 -> false)
    | uu____1208 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1216 = FStar_Syntax_Util.un_squash t in
    match uu____1216 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1226 =
          let uu____1227 = FStar_Syntax_Subst.compress t' in
          uu____1227.FStar_Syntax_Syntax.n in
        (match uu____1226 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1231 -> false)
    | uu____1232 -> false
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
            let uu____1270 = env.FStar_TypeChecker_Env.universe_of env phi in
            FStar_Syntax_Util.mk_squash uu____1270 phi in
          let uu____1271 = new_uvar reason env typ in
          bind uu____1271
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
             let uu____1327 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1327
           with | e1 -> fail "not typeable")
let must_trivial: env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1375 =
          let uu____1376 =
            let uu____1377 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1377 in
          Prims.op_Negation uu____1376 in
        if uu____1375 then fail "got non-trivial guard" else ret ()
      with | uu____1386 -> fail "got non-trivial guard"
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1394 =
      bind cur_goal
        (fun goal  ->
           let uu____1400 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1400
             (fun uu____1420  ->
                match uu____1420 with
                | (t1,typ,guard) ->
                    let uu____1432 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____1432 (fun uu____1436  -> ret typ))) in
    FStar_All.pipe_left (wrap_err "tc") uu____1394
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1457 = mk_irrelevant_goal reason env phi opts in
          bind uu____1457 (fun goal  -> add_goals [goal])
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
       let uu____1477 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1477
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1481 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1481))
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
          let uu____1498 =
            let uu____1499 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1499.FStar_TypeChecker_Env.guard_f in
          match uu____1498 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1503 = istrivial e f in
              if uu____1503
              then ret ()
              else
                (let uu____1507 = mk_irrelevant_goal reason e f opts in
                 bind uu____1507
                   (fun goal  ->
                      let goal1 =
                        let uu___73_1514 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___73_1514.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___73_1514.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___73_1514.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___73_1514.FStar_Tactics_Types.opts);
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
          let uu____1535 =
            let uu____1536 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1536.FStar_TypeChecker_Env.guard_f in
          match uu____1535 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1544 = istrivial e f in
              if uu____1544
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1552 = mk_irrelevant_goal reason e f opts in
                 bind uu____1552
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___74_1562 = goal in
                            {
                              FStar_Tactics_Types.context =
                                (uu___74_1562.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___74_1562.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___74_1562.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___74_1562.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1568 = is_irrelevant g in
       if uu____1568
       then bind dismiss (fun uu____1572  -> add_smt_goals [g])
       else
         (let uu____1574 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1574))
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
             let uu____1615 =
               try
                 let uu____1649 =
                   let uu____1658 = FStar_BigInt.to_int_fs n1 in
                   FStar_List.splitAt uu____1658 p.FStar_Tactics_Types.goals in
                 ret uu____1649
               with | uu____1680 -> fail "divide: not enough goals" in
             bind uu____1615
               (fun uu____1707  ->
                  match uu____1707 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___75_1733 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___75_1733.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___75_1733.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___75_1733.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___75_1733.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___75_1733.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___75_1733.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___75_1733.FStar_Tactics_Types.entry_range)
                        } in
                      let rp =
                        let uu___76_1735 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___76_1735.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___76_1735.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___76_1735.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___76_1735.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___76_1735.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___76_1735.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___76_1735.FStar_Tactics_Types.entry_range)
                        } in
                      let uu____1736 = set lp in
                      bind uu____1736
                        (fun uu____1744  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1758 = set rp in
                                     bind uu____1758
                                       (fun uu____1766  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___77_1782 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___77_1782.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___77_1782.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___77_1782.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___77_1782.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___77_1782.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___77_1782.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___77_1782.FStar_Tactics_Types.entry_range)
                                                      } in
                                                    let uu____1783 = set p' in
                                                    bind uu____1783
                                                      (fun uu____1791  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1809 = divide FStar_BigInt.one f idtac in
    bind uu____1809
      (fun uu____1822  -> match uu____1822 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1856::uu____1857 ->
             let uu____1860 =
               let uu____1869 = map tau in
               divide FStar_BigInt.one tau uu____1869 in
             bind uu____1860
               (fun uu____1887  ->
                  match uu____1887 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1924 =
        bind t1
          (fun uu____1929  ->
             let uu____1930 = map t2 in
             bind uu____1930 (fun uu____1938  -> ret ())) in
      focus uu____1924
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1949 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1949 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1964 =
             let uu____1965 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1965 in
           if uu____1964
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1971 = new_uvar "intro" env' typ' in
              bind uu____1971
                (fun u  ->
                   let uu____1978 =
                     let uu____1979 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1979 in
                   if uu____1978
                   then
                     let uu____1982 =
                       let uu____1985 =
                         let uu___80_1986 = goal in
                         let uu____1987 = bnorm env' u in
                         let uu____1988 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1987;
                           FStar_Tactics_Types.goal_ty = uu____1988;
                           FStar_Tactics_Types.opts =
                             (uu___80_1986.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___80_1986.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1985 in
                     bind uu____1982 (fun uu____1990  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1996 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1996)
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
       (let uu____2017 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____2017 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2036 =
              let uu____2037 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____2037 in
            if uu____2036
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____2053 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____2053; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____2055 =
                 let uu____2058 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____2058 in
               bind uu____2055
                 (fun u  ->
                    let lb =
                      let uu____2074 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2074 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2078 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2078 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2115 =
                            let uu____2118 =
                              let uu___81_2119 = goal in
                              let uu____2120 = bnorm env' u in
                              let uu____2121 =
                                let uu____2122 = comp_to_typ c in
                                bnorm env' uu____2122 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2120;
                                FStar_Tactics_Types.goal_ty = uu____2121;
                                FStar_Tactics_Types.opts =
                                  (uu___81_2119.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___81_2119.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2118 in
                          bind uu____2115
                            (fun uu____2129  ->
                               let uu____2130 =
                                 let uu____2135 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2135, b) in
                               ret uu____2130)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2149 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2149))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2173 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2173 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___82_2180 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___82_2180.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___82_2180.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___82_2180.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2198 =
          bind get
            (fun ps  ->
               let uu____2204 = __tc e t in
               bind uu____2204
                 (fun uu____2226  ->
                    match uu____2226 with
                    | (t1,uu____2236,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2242 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2242 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2198
let refine_intro: Prims.unit tac =
  let uu____2252 =
    bind cur_goal
      (fun g  ->
         let uu____2259 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
         match uu____2259 with
         | (uu____2272,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___83_2297 = g in
               {
                 FStar_Tactics_Types.context =
                   (uu___83_2297.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___83_2297.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___83_2297.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___83_2297.FStar_Tactics_Types.is_guard)
               } in
             let uu____2298 =
               let uu____2303 =
                 let uu____2308 =
                   let uu____2309 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2309] in
                 FStar_Syntax_Subst.open_term uu____2308 phi in
               match uu____2303 with
               | (bvs,phi1) ->
                   let uu____2316 =
                     let uu____2317 = FStar_List.hd bvs in
                     FStar_Pervasives_Native.fst uu____2317 in
                   (uu____2316, phi1) in
             (match uu____2298 with
              | (bv1,phi1) ->
                  let uu____2330 =
                    let uu____2333 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1 in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2333
                      g.FStar_Tactics_Types.opts in
                  bind uu____2330
                    (fun g2  ->
                       bind dismiss (fun uu____2337  -> add_goals [g1; g2])))) in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2252
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
             let uu____2361 = __tc env t in
             bind uu____2361
               (fun uu____2381  ->
                  match uu____2381 with
                  | (t1,typ,guard) ->
                      let uu____2393 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts in
                      bind uu____2393
                        (fun uu____2400  ->
                           mlog
                             (fun uu____2404  ->
                                let uu____2405 =
                                  tts goal.FStar_Tactics_Types.context typ in
                                let uu____2406 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2405
                                  uu____2406)
                             (fun uu____2409  ->
                                let uu____2410 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty in
                                if uu____2410
                                then solve goal t1
                                else
                                  (let uu____2414 =
                                     tts goal.FStar_Tactics_Types.context t1 in
                                   let uu____2415 =
                                     tts goal.FStar_Tactics_Types.context typ in
                                   let uu____2416 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty in
                                   fail3
                                     "%s : %s does not exactly solve the goal %s"
                                     uu____2414 uu____2415 uu____2416)))))
let t_exact:
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2430 =
          mlog
            (fun uu____2435  ->
               let uu____2436 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "exact: tm = %s\n" uu____2436)
            (fun uu____2439  ->
               let uu____2440 =
                 let uu____2447 =
                   __exact_now set_expected_typ1 force_guard tm in
                 trytac' uu____2447 in
               bind uu____2440
                 (fun uu___57_2456  ->
                    match uu___57_2456 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2465 =
                          let uu____2472 =
                            let uu____2475 =
                              norm [FStar_Syntax_Embeddings.Delta] in
                            bind uu____2475
                              (fun uu____2479  ->
                                 bind refine_intro
                                   (fun uu____2481  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm)) in
                          trytac' uu____2472 in
                        bind uu____2465
                          (fun uu___56_2488  ->
                             match uu___56_2488 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2496 -> fail e))) in
        FStar_All.pipe_left (wrap_err "exact") uu____2430
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2511 =
             let uu____2518 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2518 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2511 in
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
          let uu____2578 = f x in
          bind uu____2578
            (fun y  ->
               let uu____2586 = mapM f xs in
               bind uu____2586 (fun ys  -> ret (y :: ys)))
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2604 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2621 =
               let uu____2626 = t_exact false true tm in trytac uu____2626 in
             bind uu____2621
               (fun uu___58_2633  ->
                  match uu___58_2633 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2639 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2639 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2671  ->
                                let uu____2672 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2672)
                             (fun uu____2675  ->
                                let uu____2676 =
                                  let uu____2677 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2677 in
                                if uu____2676
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2681 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2681
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2701 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2701 in
                                        let uu____2702 =
                                          __apply uopt tm' typ' in
                                        bind uu____2702
                                          (fun uu____2710  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2712 =
                                               let uu____2713 =
                                                 let uu____2716 =
                                                   let uu____2717 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2717 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2716 in
                                               uu____2713.FStar_Syntax_Syntax.n in
                                             match uu____2712 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2745) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2773 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2773
                                                      then ret ()
                                                      else
                                                        (let uu____2777 =
                                                           let uu____2780 =
                                                             let uu___84_2781
                                                               = goal in
                                                             let uu____2782 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2783 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___84_2781.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2782;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2783;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___84_2781.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2780] in
                                                         add_goals uu____2777))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2829 =
        mlog
          (fun uu____2834  ->
             let uu____2835 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2835)
          (fun uu____2837  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2841 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2841
                    (fun uu____2862  ->
                       match uu____2862 with
                       | (tm1,typ,guard) ->
                           let uu____2874 =
                             let uu____2877 =
                               let uu____2880 = __apply uopt tm1 typ in
                               bind uu____2880
                                 (fun uu____2884  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2877 in
                           let uu____2885 =
                             let uu____2888 =
                               tts goal.FStar_Tactics_Types.context tm1 in
                             let uu____2889 =
                               tts goal.FStar_Tactics_Types.context typ in
                             let uu____2890 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2888 uu____2889 uu____2890 in
                           try_unif uu____2874 uu____2885))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2829
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2902 =
      let uu____2905 =
        mlog
          (fun uu____2910  ->
             let uu____2911 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2911)
          (fun uu____2914  ->
             let is_unit_t t =
               let uu____2919 =
                 let uu____2920 = FStar_Syntax_Subst.compress t in
                 uu____2920.FStar_Syntax_Syntax.n in
               match uu____2919 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____2924 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____2928 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2928
                    (fun uu____2950  ->
                       match uu____2950 with
                       | (tm1,t,guard) ->
                           let uu____2962 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____2962 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____2992 =
                                     FStar_List.fold_left
                                       (fun uu____3038  ->
                                          fun uu____3039  ->
                                            match (uu____3038, uu____3039)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____3142 =
                                                  is_unit_t b_t in
                                                if uu____3142
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3180 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____3180 with
                                                   | (u,uu____3210,g_u) ->
                                                       let uu____3224 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____3224,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____2992 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3294 =
                                         let uu____3303 =
                                           let uu____3312 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3312.FStar_Syntax_Syntax.effect_args in
                                         match uu____3303 with
                                         | pre::post::uu____3323 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3364 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3294 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3396 =
                                                let uu____3405 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3405] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3396 in
                                            let uu____3406 =
                                              let uu____3407 =
                                                let uu____3408 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3408
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3407 in
                                            if uu____3406
                                            then
                                              let uu____3411 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3412 =
                                                let uu____3413 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1 in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3413 in
                                              let uu____3414 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3411 uu____3412
                                                uu____3414
                                            else
                                              (let uu____3416 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3416
                                                 (fun uu____3421  ->
                                                    let uu____3422 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit in
                                                    bind uu____3422
                                                      (fun uu____3430  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3441 =
                                                               let uu____3448
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3448 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3441 in
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
                                                           let uu____3489 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3489
                                                           with
                                                           | (hd1,uu____3505)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3527)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3552
                                                                    -> false) in
                                                         let uu____3553 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3625
                                                                    ->
                                                                   match uu____3625
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3653)
                                                                    ->
                                                                    let uu____3654
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____3654
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3680)
                                                                    ->
                                                                    let uu____3701
                                                                    =
                                                                    let uu____3702
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3702.FStar_Syntax_Syntax.n in
                                                                    (match uu____3701
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3715
                                                                    ->
                                                                    let uu____3732
                                                                    =
                                                                    let uu____3741
                                                                    =
                                                                    let uu____3744
                                                                    =
                                                                    let uu___87_3745
                                                                    = goal in
                                                                    let uu____3746
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___87_3745.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3746;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    = typ;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___87_3745.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___87_3745.FStar_Tactics_Types.is_guard)
                                                                    } in
                                                                    [uu____3744] in
                                                                    (uu____3741,
                                                                    []) in
                                                                    ret
                                                                    uu____3732
                                                                    | 
                                                                    uu____3759
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ in
                                                                    let uu____3761
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts in
                                                                    bind
                                                                    uu____3761
                                                                    (fun
                                                                    uu___59_3777
                                                                     ->
                                                                    match uu___59_3777
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
                                                         bind uu____3553
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3845
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3845 in
                                                              let smt_goals =
                                                                let uu____3867
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_ in
                                                                FStar_List.flatten
                                                                  uu____3867 in
                                                              let rec filter'
                                                                a f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____3922
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____3922
                                                                    then
                                                                    let uu____3925
                                                                    =
                                                                    filter'
                                                                    () f xs1 in
                                                                    x ::
                                                                    uu____3925
                                                                    else
                                                                    filter'
                                                                    () f xs1 in
                                                              let sub_goals1
                                                                =
                                                                Obj.magic
                                                                  (filter' ()
                                                                    (fun a431
                                                                     ->
                                                                    fun a432 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____3939
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____3939))
                                                                    a431 a432)
                                                                    (Obj.magic
                                                                    sub_goals)) in
                                                              let uu____3940
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts in
                                                              bind uu____3940
                                                                (fun
                                                                   uu____3945
                                                                    ->
                                                                   let uu____3946
                                                                    =
                                                                    let uu____3949
                                                                    =
                                                                    let uu____3950
                                                                    =
                                                                    let uu____3951
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____3951 in
                                                                    Prims.op_Negation
                                                                    uu____3950 in
                                                                    if
                                                                    uu____3949
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret () in
                                                                   bind
                                                                    uu____3946
                                                                    (fun
                                                                    uu____3957
                                                                     ->
                                                                    let uu____3958
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals in
                                                                    bind
                                                                    uu____3958
                                                                    (fun
                                                                    uu____3962
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))) in
      focus uu____2905 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2902
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3982 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3982 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3992::(e1,uu____3994)::(e2,uu____3996)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4055 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4077 = destruct_eq' typ in
    match uu____4077 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4107 = FStar_Syntax_Util.un_squash typ in
        (match uu____4107 with
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
        let uu____4163 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____4163 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4211 = aux e' in
               FStar_Util.map_opt uu____4211
                 (fun uu____4235  ->
                    match uu____4235 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____4256 = aux e in
      FStar_Util.map_opt uu____4256
        (fun uu____4280  ->
           match uu____4280 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____4335 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____4335
            (fun uu____4359  ->
               match uu____4359 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___88_4376 = bv in
                     let uu____4377 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___88_4376.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___88_4376.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4377
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___89_4386 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___89_4386.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___89_4386.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4399 = h in
         match uu____4399 with
         | (bv,uu____4403) ->
             mlog
               (fun uu____4407  ->
                  let uu____4408 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4409 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4408
                    uu____4409)
               (fun uu____4412  ->
                  let uu____4413 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4413 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4442 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4442 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4457 =
                             let uu____4458 = FStar_Syntax_Subst.compress x in
                             uu____4458.FStar_Syntax_Syntax.n in
                           (match uu____4457 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___90_4471 = bv1 in
                                  let uu____4472 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___90_4471.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___90_4471.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4472
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4478 =
                                  let uu___91_4479 = goal in
                                  let uu____4480 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4481 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4482 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4480;
                                    FStar_Tactics_Types.witness = uu____4481;
                                    FStar_Tactics_Types.goal_ty = uu____4482;
                                    FStar_Tactics_Types.opts =
                                      (uu___91_4479.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___91_4479.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4478
                            | uu____4483 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4484 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4509 = b in
           match uu____4509 with
           | (bv,uu____4513) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___92_4517 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___92_4517.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___92_4517.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4521 =
                   let uu____4522 =
                     let uu____4529 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4529) in
                   FStar_Syntax_Syntax.NT uu____4522 in
                 [uu____4521] in
               let uu____4530 = subst_goal bv bv' s1 goal in
               (match uu____4530 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4549 = b in
         match uu____4549 with
         | (bv,uu____4553) ->
             let uu____4554 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4554 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4583 = FStar_Syntax_Util.type_u () in
                  (match uu____4583 with
                   | (ty,u) ->
                       let uu____4592 = new_uvar "binder_retype" e0 ty in
                       bind uu____4592
                         (fun t'  ->
                            let bv'' =
                              let uu___93_4602 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___93_4602.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___93_4602.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4606 =
                                let uu____4607 =
                                  let uu____4614 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4614) in
                                FStar_Syntax_Syntax.NT uu____4607 in
                              [uu____4606] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___94_4622 = b1 in
                                   let uu____4623 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___94_4622.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___94_4622.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4623
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4629  ->
                                 let uu____4630 =
                                   let uu____4633 =
                                     let uu____4636 =
                                       let uu___95_4637 = goal in
                                       let uu____4638 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4639 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4638;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4639;
                                         FStar_Tactics_Types.opts =
                                           (uu___95_4637.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___95_4637.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4636] in
                                   add_goals uu____4633 in
                                 bind uu____4630
                                   (fun uu____4642  ->
                                      let uu____4643 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4643
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4664 = b in
           match uu____4664 with
           | (bv,uu____4668) ->
               let uu____4669 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4669 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4701 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4701 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___96_4706 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___96_4706.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___96_4706.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___97_4710 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___97_4710.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___97_4710.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___97_4710.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___97_4710.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4716 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4716 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4738 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4738 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___98_4772 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___98_4772.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___98_4772.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4783 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4783 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4804 = FStar_Syntax_Print.bv_to_string x in
               let uu____4805 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4804 uu____4805
             else revert)
let free_in: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool
  =
  fun bv  ->
    fun t  ->
      let uu____4813 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____4813
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____4829  ->
              let uu____4830 = FStar_Syntax_Print.binder_to_string b in
              let uu____4831 =
                let uu____4832 =
                  let uu____4833 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context in
                  FStar_All.pipe_right uu____4833 FStar_List.length in
                FStar_All.pipe_right uu____4832 FStar_Util.string_of_int in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____4830 uu____4831)
           (fun uu____4844  ->
              let uu____4845 = split_env bv goal.FStar_Tactics_Types.context in
              match uu____4845 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____4890 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort in
                        if uu____4890
                        then
                          let uu____4893 =
                            let uu____4894 =
                              FStar_Syntax_Print.bv_to_string bv' in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____4894 in
                          fail uu____4893
                        else check bvs2 in
                  let uu____4896 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty in
                  if uu____4896
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____4900 = check bvs in
                     bind uu____4900
                       (fun uu____4906  ->
                          let env' = push_bvs e' bvs in
                          let uu____4908 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty in
                          bind uu____4908
                            (fun ut  ->
                               let uu____4914 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut in
                               if uu____4914
                               then
                                 replace_cur
                                   (let uu___99_4919 = goal in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness = ut;
                                      FStar_Tactics_Types.goal_ty =
                                        (uu___99_4919.FStar_Tactics_Types.goal_ty);
                                      FStar_Tactics_Types.opts =
                                        (uu___99_4919.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___99_4919.FStar_Tactics_Types.is_guard)
                                    })
                               else
                                 fail
                                   "Cannot clear; binder appears in witness")))))
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4926 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4926 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____4940) ->
           let uu____4945 = FStar_Syntax_Syntax.mk_binder x in
           clear uu____4945)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___100_4961 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___100_4961.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___100_4961.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___100_4961.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___100_4961.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4963  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___101_4979 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___101_4979.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___101_4979.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___101_4979.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___101_4979.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4981  -> add_goals [g']))
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
            let uu____5013 = FStar_Syntax_Subst.compress t in
            uu____5013.FStar_Syntax_Syntax.n in
          let uu____5016 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___103_5022 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___103_5022.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___103_5022.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____5016
            (fun t1  ->
               let tn1 =
                 let uu____5030 =
                   let uu____5031 = FStar_Syntax_Subst.compress t1 in
                   uu____5031.FStar_Syntax_Syntax.n in
                 match uu____5030 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____5063 = ff hd1 in
                     bind uu____5063
                       (fun hd2  ->
                          let fa uu____5083 =
                            match uu____5083 with
                            | (a,q) ->
                                let uu____5096 = ff a in
                                bind uu____5096 (fun a1  -> ret (a1, q)) in
                          let uu____5109 = mapM fa args in
                          bind uu____5109
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5169 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____5169 with
                      | (bs1,t') ->
                          let uu____5178 =
                            let uu____5181 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____5181 t' in
                          bind uu____5178
                            (fun t''  ->
                               let uu____5185 =
                                 let uu____5186 =
                                   let uu____5203 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____5204 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____5203, uu____5204, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____5186 in
                               ret uu____5185))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5225 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___102_5232 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___102_5232.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___102_5232.FStar_Syntax_Syntax.vars)
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
            let uu____5261 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____5261 with
            | (t1,lcomp,g) ->
                let uu____5273 =
                  (let uu____5276 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____5276) ||
                    (let uu____5278 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____5278) in
                if uu____5273
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____5288 = new_uvar "pointwise_rec" env typ in
                     bind uu____5288
                       (fun ut  ->
                          log ps
                            (fun uu____5299  ->
                               let uu____5300 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____5301 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5300 uu____5301);
                          (let uu____5302 =
                             let uu____5305 =
                               let uu____5306 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____5306 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5305 opts in
                           bind uu____5302
                             (fun uu____5309  ->
                                let uu____5310 =
                                  bind tau
                                    (fun uu____5316  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____5322  ->
                                            let uu____5323 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____5324 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5323 uu____5324);
                                       ret ut1) in
                                focus uu____5310))) in
                   let uu____5325 = trytac' rewrite_eq in
                   bind uu____5325
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
           let uu____5367 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5367 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5404  ->
                     let uu____5405 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5405);
                bind dismiss_all
                  (fun uu____5408  ->
                     let uu____5409 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5409
                       (fun gt'  ->
                          log ps
                            (fun uu____5419  ->
                               let uu____5420 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5420);
                          (let uu____5421 = push_goals gs in
                           bind uu____5421
                             (fun uu____5425  ->
                                add_goals
                                  [(let uu___104_5427 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___104_5427.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___104_5427.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___104_5427.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___104_5427.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5447 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5447 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5459 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5459 with
            | (hd1,args) ->
                let uu____5492 =
                  let uu____5505 =
                    let uu____5506 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5506.FStar_Syntax_Syntax.n in
                  (uu____5505, args) in
                (match uu____5492 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5520::(l,uu____5522)::(r,uu____5524)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5571 =
                       let uu____5572 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5572 in
                     if uu____5571
                     then
                       let uu____5575 = tts g.FStar_Tactics_Types.context l in
                       let uu____5576 = tts g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5575 uu____5576
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5579) ->
                     let uu____5596 = tts g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5596))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5604 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5604
         (fun u  ->
            let g' =
              let uu___105_5611 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___105_5611.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___105_5611.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___105_5611.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___105_5611.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5614  ->
                 let uu____5615 =
                   let uu____5618 =
                     let uu____5619 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5619
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5618
                     g.FStar_Tactics_Types.opts in
                 bind uu____5615
                   (fun uu____5622  ->
                      let uu____5623 = add_goals [g'] in
                      bind uu____5623 (fun uu____5627  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___106_5644 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___106_5644.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___106_5644.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___106_5644.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___106_5644.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___106_5644.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___106_5644.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___106_5644.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___106_5644.FStar_Tactics_Types.entry_range)
              })
       | uu____5645 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___107_5660 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___107_5660.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___107_5660.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___107_5660.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___107_5660.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___107_5660.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___107_5660.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___107_5660.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___107_5660.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5667 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5685 =
      bind cur_goal
        (fun g  ->
           let uu____5699 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5699
             (fun uu____5735  ->
                match uu____5735 with
                | (t1,typ,guard) ->
                    let uu____5751 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5751 with
                     | (hd1,args) ->
                         let uu____5794 =
                           let uu____5807 =
                             let uu____5808 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5808.FStar_Syntax_Syntax.n in
                           (uu____5807, args) in
                         (match uu____5794 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5827)::(q,uu____5829)::[]) when
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
                                let uu___108_5867 = g in
                                let uu____5868 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5868;
                                  FStar_Tactics_Types.witness =
                                    (uu___108_5867.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___108_5867.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___108_5867.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___108_5867.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___109_5870 = g in
                                let uu____5871 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5871;
                                  FStar_Tactics_Types.witness =
                                    (uu___109_5870.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___109_5870.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___109_5870.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___109_5870.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5878  ->
                                   let uu____5879 = add_goals [g1; g2] in
                                   bind uu____5879
                                     (fun uu____5888  ->
                                        let uu____5889 =
                                          let uu____5894 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5895 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5894, uu____5895) in
                                        ret uu____5889))
                          | uu____5900 ->
                              let uu____5913 =
                                tts g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5913)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5685
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5951 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5951);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___110_5958 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___110_5958.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___110_5958.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___110_5958.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___110_5958.FStar_Tactics_Types.is_guard)
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
      let uu____5994 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____6002 = __tc env tm in
             bind uu____6002
               (fun uu____6022  ->
                  match uu____6022 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____5994
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____6053 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6059 =
              let uu____6060 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6060 in
            new_uvar "uvar_env.2" env uu____6059 in
      bind uu____6053
        (fun typ  ->
           let uu____6072 = new_uvar "uvar_env" env typ in
           bind uu____6072 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____6084 =
      bind cur_goal
        (fun goal  ->
           let uu____6090 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____6090
             (fun uu____6110  ->
                match uu____6110 with
                | (t1,typ,guard) ->
                    let uu____6122 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____6122
                      (fun uu____6127  ->
                         let uu____6128 =
                           let uu____6131 =
                             let uu___111_6132 = goal in
                             let uu____6133 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____6134 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___111_6132.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6133;
                               FStar_Tactics_Types.goal_ty = uu____6134;
                               FStar_Tactics_Types.opts =
                                 (uu___111_6132.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____6131] in
                         add_goals uu____6128))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6084
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6152 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____6152)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6169  ->
             let uu____6170 = FStar_Options.unsafe_tactic_exec () in
             if uu____6170
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6176  -> fun uu____6177  -> false) in
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
      let uu____6197 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____6197 with
      | (u,uu____6215,g_u) ->
          let g =
            let uu____6230 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6230;
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
      let uu____6245 = goal_of_goal_ty env typ in
      match uu____6245 with
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