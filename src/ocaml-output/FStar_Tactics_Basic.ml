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
  'Auu____88 .
    'Auu____88 tac ->
      FStar_Tactics_Types.proofstate ->
        'Auu____88 FStar_Tactics_Result.__result
  = fun t  -> fun p  -> t.tac_f p
let ret: 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p))
let bind: 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____155 = run t1 p in
           match uu____155 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____162 = t2 a in run uu____162 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: FStar_Tactics_Types.goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____174 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____174
        (FStar_Syntax_Print.binders_to_string ", ") in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
    let uu____177 =
      FStar_TypeChecker_Normalize.term_to_string
        g.FStar_Tactics_Types.context w in
    let uu____178 =
      FStar_TypeChecker_Normalize.term_to_string
        g.FStar_Tactics_Types.context t in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____177 uu____178
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____191 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____191
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____204 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____204
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____221 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____221
let comp_to_typ: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____227) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____237) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: FStar_Tactics_Types.goal -> Prims.bool =
  fun g  ->
    let uu____251 =
      let uu____256 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty in
      FStar_Syntax_Util.un_squash uu____256 in
    match uu____251 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____262 -> false
let dump_goal:
  'Auu____273 . 'Auu____273 -> FStar_Tactics_Types.goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____283 = goal_to_string goal in tacprint uu____283
let dump_cur: FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____293 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____297 = FStar_List.hd ps.FStar_Tactics_Types.goals in
            dump_goal ps uu____297))
let ps_to_string:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu____305  ->
    match uu____305 with
    | (msg,ps) ->
        let uu____312 =
          let uu____315 =
            let uu____316 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____316 msg in
          let uu____317 =
            let uu____320 =
              let uu____321 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range in
              FStar_Util.format1 "Position: %s\n" uu____321 in
            let uu____322 =
              let uu____325 =
                let uu____326 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals) in
                let uu____327 =
                  let uu____328 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals in
                  FStar_String.concat "\n" uu____328 in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____326
                  uu____327 in
              let uu____331 =
                let uu____334 =
                  let uu____335 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals) in
                  let uu____336 =
                    let uu____337 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals in
                    FStar_String.concat "\n" uu____337 in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____335
                    uu____336 in
                [uu____334] in
              uu____325 :: uu____331 in
            uu____320 :: uu____322 in
          uu____315 :: uu____317 in
        FStar_String.concat "" uu____312
let goal_to_json: FStar_Tactics_Types.goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____345 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____345 FStar_Syntax_Print.binders_to_json in
    let uu____346 =
      let uu____353 =
        let uu____360 =
          let uu____365 =
            let uu____366 =
              let uu____373 =
                let uu____378 =
                  let uu____379 =
                    FStar_TypeChecker_Normalize.term_to_string
                      g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness in
                  FStar_Util.JsonStr uu____379 in
                ("witness", uu____378) in
              let uu____380 =
                let uu____387 =
                  let uu____392 =
                    let uu____393 =
                      FStar_TypeChecker_Normalize.term_to_string
                        g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty in
                    FStar_Util.JsonStr uu____393 in
                  ("type", uu____392) in
                [uu____387] in
              uu____373 :: uu____380 in
            FStar_Util.JsonAssoc uu____366 in
          ("goal", uu____365) in
        [uu____360] in
      ("hyps", g_binders) :: uu____353 in
    FStar_Util.JsonAssoc uu____346
let ps_to_json:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____425  ->
    match uu____425 with
    | (msg,ps) ->
        let uu____432 =
          let uu____439 =
            let uu____446 =
              let uu____451 =
                let uu____452 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals in
                FStar_Util.JsonList uu____452 in
              ("goals", uu____451) in
            let uu____455 =
              let uu____462 =
                let uu____467 =
                  let uu____468 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals in
                  FStar_Util.JsonList uu____468 in
                ("smt-goals", uu____467) in
              [uu____462] in
            uu____446 :: uu____455 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____439 in
        FStar_Util.JsonAssoc uu____432
let dump_proofstate:
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____497  ->
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
         (let uu____519 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_cur uu____519 msg);
         FStar_Tactics_Result.Success ((), ps))
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc in
         (let uu____536 = FStar_Tactics_Types.subst_proof_state subst1 ps in
          dump_proofstate uu____536 msg);
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
      let uu____567 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____567 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____621 =
              let uu____624 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____624 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____621);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: 'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac
  = fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ())
let fail: 'Auu____714 . Prims.string -> 'Auu____714 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____725 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____725
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____733 . Prims.string -> Prims.string -> 'Auu____733 tac =
  fun msg  ->
    fun x  -> let uu____744 = FStar_Util.format1 msg x in fail uu____744
let fail2:
  'Auu____753 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____753 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____768 = FStar_Util.format2 msg x y in fail uu____768
let fail3:
  'Auu____779 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____779 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____798 = FStar_Util.format3 msg x y z in fail uu____798
let trytac': 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____830 = run t ps in
         match uu____830 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____851) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____878 = trytac' t in
    bind uu____878
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____905 -> ret FStar_Pervasives_Native.None)
let wrap_err: 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____934 = run t ps in
           match uu____934 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____952  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____970 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____984 =
         let uu___144_985 = p in
         let uu____986 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___144_985.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___144_985.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___144_985.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____986;
           FStar_Tactics_Types.smt_goals =
             (uu___144_985.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___144_985.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___144_985.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___144_985.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___144_985.FStar_Tactics_Types.entry_range)
         } in
       set uu____984)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____1001 = trysolve goal solution in
      if uu____1001
      then dismiss
      else
        (let uu____1005 =
           let uu____1006 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____1007 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____1008 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____1006
             uu____1007 uu____1008 in
         fail uu____1005)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___145_1015 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___145_1015.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___145_1015.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___145_1015.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___145_1015.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___145_1015.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___145_1015.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___145_1015.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___145_1015.FStar_Tactics_Types.entry_range)
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
      let uu____1031 = FStar_TypeChecker_Env.pop_bv e in
      match uu____1031 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
          aux b4 e1 in
    let uu____1049 =
      let uu____1050 = aux b2 env in Prims.op_Negation uu____1050 in
    if uu____1049
    then
      let uu____1051 =
        let uu____1052 = goal_to_string g in
        FStar_Util.format1
          "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
          uu____1052 in
      FStar_Errors.warn
        (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____1051
    else ()
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___146_1072 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___146_1072.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___146_1072.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___146_1072.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___146_1072.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___146_1072.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___146_1072.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___146_1072.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___146_1072.FStar_Tactics_Types.entry_range)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___147_1091 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___147_1091.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___147_1091.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___147_1091.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___147_1091.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___147_1091.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___147_1091.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___147_1091.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___147_1091.FStar_Tactics_Types.entry_range)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___148_1110 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___148_1110.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___148_1110.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___148_1110.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___148_1110.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___148_1110.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___148_1110.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___148_1110.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___148_1110.FStar_Tactics_Types.entry_range)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___149_1129 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___149_1129.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___149_1129.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___149_1129.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___149_1129.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___149_1129.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___149_1129.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___149_1129.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___149_1129.FStar_Tactics_Types.entry_range)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1139  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___150_1152 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___150_1152.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___150_1152.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___150_1152.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___150_1152.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___150_1152.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___150_1152.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___150_1152.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___150_1152.FStar_Tactics_Types.entry_range)
            }))
let new_uvar:
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1181 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ in
        match uu____1181 with
        | (u,uu____1197,g_u) ->
            let uu____1211 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits in
            bind uu____1211 (fun uu____1215  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1220 = FStar_Syntax_Util.un_squash t in
    match uu____1220 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1230 =
          let uu____1231 = FStar_Syntax_Subst.compress t' in
          uu____1231.FStar_Syntax_Syntax.n in
        (match uu____1230 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1235 -> false)
    | uu____1236 -> false
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
          let typ = FStar_Syntax_Util.mk_squash phi in
          let uu____1303 = new_uvar reason env typ in
          bind uu____1303
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
             let uu____1361 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t in
             ret uu____1361
           with | e1 -> fail "not typeable")
let must_trivial: env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1411 =
          let uu____1412 =
            let uu____1413 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1413 in
          Prims.op_Negation uu____1412 in
        if uu____1411 then fail "got non-trivial guard" else ret ()
      with | uu____1422 -> fail "got non-trivial guard"
let tc: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1431 =
      bind cur_goal
        (fun goal  ->
           let uu____1437 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____1437
             (fun uu____1457  ->
                match uu____1457 with
                | (t1,typ,guard) ->
                    let uu____1469 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____1469 (fun uu____1473  -> ret typ))) in
    FStar_All.pipe_left (wrap_err "tc") uu____1431
let add_irrelevant_goal:
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1498 = mk_irrelevant_goal reason env phi opts in
          bind uu____1498 (fun goal  -> add_goals [goal])
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
       let uu____1520 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1520
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1524 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1524))
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
          let uu____1545 =
            let uu____1546 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1546.FStar_TypeChecker_Env.guard_f in
          match uu____1545 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1550 = istrivial e f in
              if uu____1550
              then ret ()
              else
                (let uu____1554 = mk_irrelevant_goal reason e f opts in
                 bind uu____1554
                   (fun goal  ->
                      let goal1 =
                        let uu___155_1561 = goal in
                        {
                          FStar_Tactics_Types.context =
                            (uu___155_1561.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___155_1561.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___155_1561.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___155_1561.FStar_Tactics_Types.opts);
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
          let uu____1586 =
            let uu____1587 = FStar_TypeChecker_Rel.simplify_guard e g in
            uu____1587.FStar_TypeChecker_Env.guard_f in
          match uu____1586 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1595 = istrivial e f in
              if uu____1595
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1603 = mk_irrelevant_goal reason e f opts in
                 bind uu____1603
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___156_1613 = goal in
                            {
                              FStar_Tactics_Types.context =
                                (uu___156_1613.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___156_1613.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___156_1613.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___156_1613.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1619 = is_irrelevant g in
       if uu____1619
       then bind dismiss (fun uu____1623  -> add_smt_goals [g])
       else
         (let uu____1625 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1625))
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
             let uu____1671 =
               try
                 let uu____1705 =
                   let uu____1714 = FStar_BigInt.to_int_fs n1 in
                   FStar_List.splitAt uu____1714 p.FStar_Tactics_Types.goals in
                 ret uu____1705
               with | uu____1736 -> fail "divide: not enough goals" in
             bind uu____1671
               (fun uu____1763  ->
                  match uu____1763 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___157_1789 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___157_1789.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___157_1789.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___157_1789.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___157_1789.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___157_1789.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___157_1789.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___157_1789.FStar_Tactics_Types.entry_range)
                        } in
                      let rp =
                        let uu___158_1791 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___158_1791.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___158_1791.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___158_1791.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___158_1791.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___158_1791.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___158_1791.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___158_1791.FStar_Tactics_Types.entry_range)
                        } in
                      let uu____1792 = set lp in
                      bind uu____1792
                        (fun uu____1800  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1814 = set rp in
                                     bind uu____1814
                                       (fun uu____1822  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___159_1838 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___159_1838.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___159_1838.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___159_1838.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___159_1838.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___159_1838.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___159_1838.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___159_1838.FStar_Tactics_Types.entry_range)
                                                      } in
                                                    let uu____1839 = set p' in
                                                    bind uu____1839
                                                      (fun uu____1847  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1867 = divide FStar_BigInt.one f idtac in
    bind uu____1867
      (fun uu____1880  -> match uu____1880 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1915::uu____1916 ->
             let uu____1919 =
               let uu____1928 = map tau in
               divide FStar_BigInt.one tau uu____1928 in
             bind uu____1919
               (fun uu____1946  ->
                  match uu____1946 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1985 =
        bind t1
          (fun uu____1990  ->
             let uu____1991 = map t2 in
             bind uu____1991 (fun uu____1999  -> ret ())) in
      focus uu____1985
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____2010 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____2010 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2025 =
             let uu____2026 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____2026 in
           if uu____2025
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____2032 = new_uvar "intro" env' typ' in
              bind uu____2032
                (fun u  ->
                   let uu____2039 =
                     let uu____2040 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____2040 in
                   if uu____2039
                   then
                     let uu____2043 =
                       let uu____2046 =
                         let uu___162_2047 = goal in
                         let uu____2048 = bnorm env' u in
                         let uu____2049 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2048;
                           FStar_Tactics_Types.goal_ty = uu____2049;
                           FStar_Tactics_Types.opts =
                             (uu___162_2047.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___162_2047.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____2046 in
                     bind uu____2043 (fun uu____2051  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2057 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____2057)
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
       (let uu____2078 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____2078 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2097 =
              let uu____2098 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____2098 in
            if uu____2097
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____2114 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____2114; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____2116 =
                 let uu____2119 = comp_to_typ c in
                 new_uvar "intro_rec" env' uu____2119 in
               bind uu____2116
                 (fun u  ->
                    let lb =
                      let uu____2135 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2135 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____2139 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____2139 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____2176 =
                            let uu____2179 =
                              let uu___163_2180 = goal in
                              let uu____2181 = bnorm env' u in
                              let uu____2182 =
                                let uu____2183 = comp_to_typ c in
                                bnorm env' uu____2183 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2181;
                                FStar_Tactics_Types.goal_ty = uu____2182;
                                FStar_Tactics_Types.opts =
                                  (uu___163_2180.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___163_2180.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____2179 in
                          bind uu____2176
                            (fun uu____2190  ->
                               let uu____2191 =
                                 let uu____2196 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____2196, b) in
                               ret uu____2191)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2210 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2210))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2235 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2235 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___164_2242 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___164_2242.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___164_2242.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___164_2242.FStar_Tactics_Types.is_guard)
            }))
let norm_term_env:
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2263 =
          bind get
            (fun ps  ->
               let uu____2269 = __tc e t in
               bind uu____2269
                 (fun uu____2291  ->
                    match uu____2291 with
                    | (t1,uu____2301,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2307 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2307 in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1 in
                          ret t2)))) in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2263
let refine_intro: Prims.unit tac =
  let uu____2317 =
    bind cur_goal
      (fun g  ->
         let uu____2324 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
         match uu____2324 with
         | (uu____2337,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___165_2362 = g in
               {
                 FStar_Tactics_Types.context =
                   (uu___165_2362.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___165_2362.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___165_2362.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___165_2362.FStar_Tactics_Types.is_guard)
               } in
             let uu____2363 =
               let uu____2368 =
                 let uu____2373 =
                   let uu____2374 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2374] in
                 FStar_Syntax_Subst.open_term uu____2373 phi in
               match uu____2368 with
               | (bvs,phi1) ->
                   let uu____2381 =
                     let uu____2382 = FStar_List.hd bvs in
                     FStar_Pervasives_Native.fst uu____2382 in
                   (uu____2381, phi1) in
             (match uu____2363 with
              | (bv1,phi1) ->
                  let uu____2395 =
                    let uu____2398 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1 in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2398
                      g.FStar_Tactics_Types.opts in
                  bind uu____2395
                    (fun g2  ->
                       bind dismiss (fun uu____2402  -> add_goals [g1; g2])))) in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2317
let __exact_now: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun force_guard  ->
    fun t  ->
      bind cur_goal
        (fun goal  ->
           let uu____2422 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____2422
             (fun uu____2442  ->
                match uu____2442 with
                | (t1,typ,guard) ->
                    let uu____2454 =
                      if force_guard
                      then
                        must_trivial goal.FStar_Tactics_Types.context guard
                      else
                        add_goal_from_guard "__exact typing"
                          goal.FStar_Tactics_Types.context guard
                          goal.FStar_Tactics_Types.opts in
                    bind uu____2454
                      (fun uu____2462  ->
                         let uu____2463 =
                           do_unify goal.FStar_Tactics_Types.context typ
                             goal.FStar_Tactics_Types.goal_ty in
                         if uu____2463
                         then solve goal t1
                         else
                           (let uu____2467 =
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context t1 in
                            let uu____2468 =
                              let uu____2469 =
                                bnorm goal.FStar_Tactics_Types.context typ in
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context uu____2469 in
                            let uu____2470 =
                              FStar_TypeChecker_Normalize.term_to_string
                                goal.FStar_Tactics_Types.context
                                goal.FStar_Tactics_Types.goal_ty in
                            fail3
                              "%s : %s does not exactly solve the goal %s"
                              uu____2467 uu____2468 uu____2470))))
let __exact: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun force_guard  ->
    fun t  ->
      let uu____2483 =
        let uu____2490 = __exact_now force_guard t in trytac' uu____2490 in
      bind uu____2483
        (fun uu___139_2499  ->
           match uu___139_2499 with
           | FStar_Util.Inr r -> ret ()
           | FStar_Util.Inl e ->
               let uu____2508 =
                 let uu____2515 =
                   let uu____2518 = norm [FStar_Syntax_Embeddings.Delta] in
                   bind uu____2518
                     (fun uu____2522  ->
                        bind refine_intro
                          (fun uu____2524  -> __exact_now force_guard t)) in
                 trytac' uu____2515 in
               bind uu____2508
                 (fun uu___138_2531  ->
                    match uu___138_2531 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl uu____2539 -> fail e))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2548 =
      mlog
        (fun uu____2553  ->
           let uu____2554 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact: tm = %s\n" uu____2554)
        (fun uu____2557  ->
           let uu____2558 = __exact true tm in focus uu____2558) in
    FStar_All.pipe_left (wrap_err "exact") uu____2548
let exact_guard: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2573 =
      mlog
        (fun uu____2578  ->
           let uu____2579 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "exact_guard: tm = %s\n" uu____2579)
        (fun uu____2582  ->
           let uu____2583 = __exact false tm in focus uu____2583) in
    FStar_All.pipe_left (wrap_err "exact_guard") uu____2573
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2602 =
             let uu____2609 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2609 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2602 in
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
          let uu____2673 = f x in
          bind uu____2673
            (fun y  ->
               let uu____2681 = mapM f xs in
               bind uu____2681 (fun ys  -> ret (y :: ys)))
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
             let uu____2720 =
               let uu____2725 = __exact true tm in trytac uu____2725 in
             bind uu____2720
               (fun uu___140_2732  ->
                  match uu___140_2732 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2738 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2738 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2770  ->
                                let uu____2771 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq) in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2771)
                             (fun uu____2774  ->
                                let uu____2775 =
                                  let uu____2776 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____2776 in
                                if uu____2775
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2780 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____2780
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                        let typ' =
                                          let uu____2800 = comp_to_typ c in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2800 in
                                        let uu____2801 =
                                          __apply uopt tm' typ' in
                                        bind uu____2801
                                          (fun uu____2809  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u in
                                             let uu____2811 =
                                               let uu____2812 =
                                                 let uu____2815 =
                                                   let uu____2816 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1 in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2816 in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2815 in
                                               uu____2812.FStar_Syntax_Syntax.n in
                                             match uu____2811 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2844) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2872 =
                                                        uopt &&
                                                          (uvar_free uvar ps) in
                                                      if uu____2872
                                                      then ret ()
                                                      else
                                                        (let uu____2876 =
                                                           let uu____2879 =
                                                             let uu___166_2880
                                                               = goal in
                                                             let uu____2881 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1 in
                                                             let uu____2882 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___166_2880.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2881;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2882;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___166_2880.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             } in
                                                           [uu____2879] in
                                                         add_goals uu____2876))
                                             | t -> ret ())))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2933 =
        mlog
          (fun uu____2938  ->
             let uu____2939 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply: tm = %s\n" uu____2939)
          (fun uu____2941  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2945 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____2945
                    (fun uu____2966  ->
                       match uu____2966 with
                       | (tm1,typ,guard) ->
                           let uu____2978 =
                             let uu____2981 =
                               let uu____2984 = __apply uopt tm1 typ in
                               bind uu____2984
                                 (fun uu____2988  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts) in
                             focus uu____2981 in
                           let uu____2989 =
                             let uu____2992 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context tm1 in
                             let uu____2993 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context typ in
                             let uu____2994 =
                               FStar_TypeChecker_Normalize.term_to_string
                                 goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2992 uu____2993 uu____2994 in
                           try_unif uu____2978 uu____2989))) in
      FStar_All.pipe_left (wrap_err "apply") uu____2933
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____3007 =
      let uu____3010 =
        mlog
          (fun uu____3015  ->
             let uu____3016 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3016)
          (fun uu____3019  ->
             let is_unit_t t =
               let uu____3024 =
                 let uu____3025 = FStar_Syntax_Subst.compress t in
                 uu____3025.FStar_Syntax_Syntax.n in
               match uu____3024 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3029 -> false in
             bind cur_goal
               (fun goal  ->
                  let uu____3033 = __tc goal.FStar_Tactics_Types.context tm in
                  bind uu____3033
                    (fun uu____3055  ->
                       match uu____3055 with
                       | (tm1,t,guard) ->
                           let uu____3067 =
                             FStar_Syntax_Util.arrow_formals_comp t in
                           (match uu____3067 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3097 =
                                     FStar_List.fold_left
                                       (fun uu____3143  ->
                                          fun uu____3144  ->
                                            match (uu____3143, uu____3144)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort in
                                                let uu____3247 =
                                                  is_unit_t b_t in
                                                if uu____3247
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3285 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t in
                                                   match uu____3285 with
                                                   | (u,uu____3315,g_u) ->
                                                       let uu____3329 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u in
                                                       (((u, aq) :: uvs),
                                                         uu____3329,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs in
                                   match uu____3097 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp in
                                       let uu____3399 =
                                         let uu____3408 =
                                           let uu____3417 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1 in
                                           uu____3417.FStar_Syntax_Syntax.effect_args in
                                         match uu____3408 with
                                         | pre::post::uu____3428 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3469 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma" in
                                       (match uu____3399 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3501 =
                                                let uu____3510 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit in
                                                [uu____3510] in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3501 in
                                            let uu____3511 =
                                              let uu____3512 =
                                                let uu____3513 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3513
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              Prims.op_Negation uu____3512 in
                                            if uu____3511
                                            then
                                              let uu____3516 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  tm1 in
                                              let uu____3517 =
                                                let uu____3518 =
                                                  FStar_Syntax_Util.mk_squash
                                                    post1 in
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3518 in
                                              let uu____3519 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3516 uu____3517
                                                uu____3519
                                            else
                                              (let solution =
                                                 let uu____3522 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3522 in
                                               let uu____3523 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits in
                                               bind uu____3523
                                                 (fun uu____3528  ->
                                                    let uu____3529 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit in
                                                    bind uu____3529
                                                      (fun uu____3537  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3548 =
                                                               let uu____3555
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1 in
                                                               FStar_Util.set_elements
                                                                 uu____3555 in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3548 in
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
                                                           let uu____3596 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1 in
                                                           match uu____3596
                                                           with
                                                           | (hd1,uu____3612)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3634)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3659
                                                                    -> false) in
                                                         let uu____3660 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3714
                                                                    ->
                                                                   match uu____3714
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3736)
                                                                    ->
                                                                    let uu____3737
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____3737
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3757)
                                                                    ->
                                                                    let uu____3778
                                                                    =
                                                                    let uu____3779
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1 in
                                                                    uu____3779.FStar_Syntax_Syntax.n in
                                                                    (match uu____3778
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3786
                                                                    ->
                                                                    let uu____3803
                                                                    =
                                                                    let uu____3806
                                                                    =
                                                                    let uu___169_3807
                                                                    = goal in
                                                                    let uu____3808
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term in
                                                                    let uu____3809
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___169_3807.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3808;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3809;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___169_3807.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___169_3807.FStar_Tactics_Types.is_guard)
                                                                    } in
                                                                    [uu____3806] in
                                                                    ret
                                                                    uu____3803
                                                                    | 
                                                                    uu____3812
                                                                    ->
                                                                    let term1
                                                                    =
                                                                    bnorm env
                                                                    term in
                                                                    let uu____3814
                                                                    =
                                                                    let uu____3821
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3821
                                                                    term1 in
                                                                    (match uu____3814
                                                                    with
                                                                    | 
                                                                    (uu____3826,uu____3827,g_typ)
                                                                    ->
                                                                    let uu____3829
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts in
                                                                    bind
                                                                    uu____3829
                                                                    (fun
                                                                    uu___141_3839
                                                                     ->
                                                                    match uu___141_3839
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    ret []
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g ->
                                                                    ret [g])))))) in
                                                         bind uu____3660
                                                           (fun sub_goals_ 
                                                              ->
                                                              let sub_goals =
                                                                FStar_List.flatten
                                                                  sub_goals_ in
                                                              let rec filter'
                                                                f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____3905
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____3905
                                                                    then
                                                                    let uu____3908
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____3908
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                              let sub_goals1
                                                                =
                                                                filter'
                                                                  (fun g  ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____3922
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____3922)
                                                                  sub_goals in
                                                              let uu____3923
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts in
                                                              bind uu____3923
                                                                (fun
                                                                   uu____3928
                                                                    ->
                                                                   let uu____3929
                                                                    =
                                                                    let uu____3932
                                                                    =
                                                                    let uu____3933
                                                                    =
                                                                    let uu____3934
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____3934 in
                                                                    Prims.op_Negation
                                                                    uu____3933 in
                                                                    if
                                                                    uu____3932
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret () in
                                                                   bind
                                                                    uu____3929
                                                                    (fun
                                                                    uu____3939
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1)))))))))))) in
      focus uu____3010 in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3007
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3960 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3960 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3970::(e1,uu____3972)::(e2,uu____3974)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4033 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4056 = destruct_eq' typ in
    match uu____4056 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4086 = FStar_Syntax_Util.un_squash typ in
        (match uu____4086 with
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
        let uu____4144 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____4144 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4192 = aux e' in
               FStar_Util.map_opt uu____4192
                 (fun uu____4216  ->
                    match uu____4216 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____4237 = aux e in
      FStar_Util.map_opt uu____4237
        (fun uu____4261  ->
           match uu____4261 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
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
          let uu____4322 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____4322
            (fun uu____4346  ->
               match uu____4346 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___170_4363 = bv in
                     let uu____4364 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___170_4363.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___170_4363.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4364
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___171_4373 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___171_4373.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___171_4373.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4387 = h in
         match uu____4387 with
         | (bv,uu____4391) ->
             mlog
               (fun uu____4395  ->
                  let uu____4396 = FStar_Syntax_Print.bv_to_string bv in
                  let uu____4397 =
                    FStar_Syntax_Print.term_to_string
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4396
                    uu____4397)
               (fun uu____4400  ->
                  let uu____4401 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____4401 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4430 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____4430 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4445 =
                             let uu____4446 = FStar_Syntax_Subst.compress x in
                             uu____4446.FStar_Syntax_Syntax.n in
                           (match uu____4445 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___172_4459 = bv1 in
                                  let uu____4460 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___172_4459.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___172_4459.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4460
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____4466 =
                                  let uu___173_4467 = goal in
                                  let uu____4468 = push_bvs e0 (bv :: bvs1) in
                                  let uu____4469 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____4470 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____4468;
                                    FStar_Tactics_Types.witness = uu____4469;
                                    FStar_Tactics_Types.goal_ty = uu____4470;
                                    FStar_Tactics_Types.opts =
                                      (uu___173_4467.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___173_4467.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____4466
                            | uu____4471 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4472 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4499 = b in
           match uu____4499 with
           | (bv,uu____4503) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___174_4507 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___174_4507.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___174_4507.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____4511 =
                   let uu____4512 =
                     let uu____4519 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____4519) in
                   FStar_Syntax_Syntax.NT uu____4512 in
                 [uu____4511] in
               let uu____4520 = subst_goal bv bv' s1 goal in
               (match uu____4520 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4540 = b in
         match uu____4540 with
         | (bv,uu____4544) ->
             let uu____4545 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4545 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4574 = FStar_Syntax_Util.type_u () in
                  (match uu____4574 with
                   | (ty,u) ->
                       let uu____4583 = new_uvar "binder_retype" e0 ty in
                       bind uu____4583
                         (fun t'  ->
                            let bv'' =
                              let uu___175_4593 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___175_4593.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___175_4593.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4597 =
                                let uu____4598 =
                                  let uu____4605 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4605) in
                                FStar_Syntax_Syntax.NT uu____4598 in
                              [uu____4597] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___176_4613 = b1 in
                                   let uu____4614 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___176_4613.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___176_4613.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4614
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4620  ->
                                 let uu____4621 =
                                   let uu____4624 =
                                     let uu____4627 =
                                       let uu___177_4628 = goal in
                                       let uu____4629 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4630 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4629;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4630;
                                         FStar_Tactics_Types.opts =
                                           (uu___177_4628.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___177_4628.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4627] in
                                   add_goals uu____4624 in
                                 bind uu____4621
                                   (fun uu____4633  ->
                                      let uu____4634 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4634
                                        goal.FStar_Tactics_Types.opts))))))
let norm_binder_type:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4657 = b in
           match uu____4657 with
           | (bv,uu____4661) ->
               let uu____4662 = split_env bv goal.FStar_Tactics_Types.context in
               (match uu____4662 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4694 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4694 in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort in
                    let bv' =
                      let uu___178_4699 = bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___178_4699.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___178_4699.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      } in
                    let env' = push_bvs e0 (bv' :: bvs) in
                    replace_cur
                      (let uu___179_4703 = goal in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___179_4703.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___179_4703.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___179_4703.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___179_4703.FStar_Tactics_Types.is_guard)
                       })))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4709 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4709 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4731 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4731 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___180_4765 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___180_4765.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___180_4765.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4777 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4777 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4798 = FStar_Syntax_Print.bv_to_string x in
               let uu____4799 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4798 uu____4799
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4806 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4806 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4828 = FStar_Util.set_mem x fns_ty in
           if uu____4828
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4832 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4832
                (fun u  ->
                   let uu____4838 =
                     let uu____4839 = trysolve goal u in
                     Prims.op_Negation uu____4839 in
                   if uu____4838
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___181_4844 = goal in
                        let uu____4845 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4845;
                          FStar_Tactics_Types.goal_ty =
                            (uu___181_4844.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___181_4844.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___181_4844.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4847  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4859 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4859 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4883  ->
                    let uu____4884 = clear b in
                    bind uu____4884
                      (fun uu____4888  ->
                         bind intro (fun uu____4890  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___182_4907 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___182_4907.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___182_4907.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___182_4907.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___182_4907.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4909  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___183_4926 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___183_4926.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___183_4926.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___183_4926.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___183_4926.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4928  -> add_goals [g']))
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
            let uu____4964 = FStar_Syntax_Subst.compress t in
            uu____4964.FStar_Syntax_Syntax.n in
          let uu____4967 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___185_4973 = t in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___185_4973.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___185_4973.FStar_Syntax_Syntax.vars)
                 })
            else ret t in
          bind uu____4967
            (fun t1  ->
               let tn1 =
                 let uu____4981 =
                   let uu____4982 = FStar_Syntax_Subst.compress t1 in
                   uu____4982.FStar_Syntax_Syntax.n in
                 match uu____4981 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env in
                     let uu____5014 = ff hd1 in
                     bind uu____5014
                       (fun hd2  ->
                          let fa uu____5034 =
                            match uu____5034 with
                            | (a,q) ->
                                let uu____5047 = ff a in
                                bind uu____5047 (fun a1  -> ret (a1, q)) in
                          let uu____5060 = mapM fa args in
                          bind uu____5060
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5120 = FStar_Syntax_Subst.open_term bs t2 in
                     (match uu____5120 with
                      | (bs1,t') ->
                          let uu____5129 =
                            let uu____5132 =
                              FStar_TypeChecker_Env.push_binders env bs1 in
                            tac_fold_env d f uu____5132 t' in
                          bind uu____5129
                            (fun t''  ->
                               let uu____5136 =
                                 let uu____5137 =
                                   let uu____5154 =
                                     FStar_Syntax_Subst.close_binders bs1 in
                                   let uu____5155 =
                                     FStar_Syntax_Subst.close bs1 t'' in
                                   (uu____5154, uu____5155, k) in
                                 FStar_Syntax_Syntax.Tm_abs uu____5137 in
                               ret uu____5136))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5176 -> ret tn in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___184_5183 = t1 in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___184_5183.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___184_5183.FStar_Syntax_Syntax.vars)
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
            let uu____5217 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____5217 with
            | (t1,lcomp,g) ->
                let uu____5229 =
                  (let uu____5232 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____5232) ||
                    (let uu____5234 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____5234) in
                if uu____5229
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                     let uu____5244 = new_uvar "pointwise_rec" env typ in
                     bind uu____5244
                       (fun ut  ->
                          log ps
                            (fun uu____5255  ->
                               let uu____5256 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____5257 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5256 uu____5257);
                          (let uu____5258 =
                             let uu____5261 =
                               let uu____5262 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ in
                               FStar_Syntax_Util.mk_eq2 uu____5262 typ t1 ut in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5261 opts in
                           bind uu____5258
                             (fun uu____5265  ->
                                let uu____5266 =
                                  bind tau
                                    (fun uu____5272  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut in
                                       log ps
                                         (fun uu____5278  ->
                                            let uu____5279 =
                                              FStar_Syntax_Print.term_to_string
                                                t1 in
                                            let uu____5280 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1 in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5279 uu____5280);
                                       ret ut1) in
                                focus uu____5266))) in
                   let uu____5281 = trytac' rewrite_eq in
                   bind uu____5281
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
           let uu____5325 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals" in
           match uu____5325 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty in
               (log ps
                  (fun uu____5362  ->
                     let uu____5363 = FStar_Syntax_Print.term_to_string gt1 in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5363);
                bind dismiss_all
                  (fun uu____5366  ->
                     let uu____5367 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1 in
                     bind uu____5367
                       (fun gt'  ->
                          log ps
                            (fun uu____5377  ->
                               let uu____5378 =
                                 FStar_Syntax_Print.term_to_string gt' in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5378);
                          (let uu____5379 = push_goals gs in
                           bind uu____5379
                             (fun uu____5383  ->
                                add_goals
                                  [(let uu___186_5385 = g in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___186_5385.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___186_5385.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___186_5385.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___186_5385.FStar_Tactics_Types.is_guard)
                                    })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5405 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____5405 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5417 = FStar_Syntax_Util.head_and_args' t in
           (match uu____5417 with
            | (hd1,args) ->
                let uu____5450 =
                  let uu____5463 =
                    let uu____5464 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____5464.FStar_Syntax_Syntax.n in
                  (uu____5463, args) in
                (match uu____5450 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5478::(l,uu____5480)::(r,uu____5482)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5529 =
                       let uu____5530 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____5530 in
                     if uu____5529
                     then
                       let uu____5533 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____5534 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5533 uu____5534
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5537) ->
                     let uu____5554 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5554))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5562 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty in
       bind uu____5562
         (fun u  ->
            let g' =
              let uu___187_5569 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___187_5569.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___187_5569.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___187_5569.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___187_5569.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5572  ->
                 let uu____5573 =
                   let uu____5576 =
                     let uu____5577 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5577
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5576
                     g.FStar_Tactics_Types.opts in
                 bind uu____5573
                   (fun uu____5580  ->
                      let uu____5581 = add_goals [g'] in
                      bind uu____5581 (fun uu____5585  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___188_5602 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___188_5602.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___188_5602.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___188_5602.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___188_5602.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___188_5602.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___188_5602.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___188_5602.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___188_5602.FStar_Tactics_Types.entry_range)
              })
       | uu____5603 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___189_5618 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___189_5618.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___189_5618.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___189_5618.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___189_5618.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___189_5618.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___189_5618.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___189_5618.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___189_5618.FStar_Tactics_Types.entry_range)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5625 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____5644 =
      bind cur_goal
        (fun g  ->
           let uu____5658 = __tc g.FStar_Tactics_Types.context t in
           bind uu____5658
             (fun uu____5694  ->
                match uu____5694 with
                | (t1,typ,guard) ->
                    let uu____5710 = FStar_Syntax_Util.head_and_args typ in
                    (match uu____5710 with
                     | (hd1,args) ->
                         let uu____5753 =
                           let uu____5766 =
                             let uu____5767 = FStar_Syntax_Util.un_uinst hd1 in
                             uu____5767.FStar_Syntax_Syntax.n in
                           (uu____5766, args) in
                         (match uu____5753 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5786)::(q,uu____5788)::[]) when
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
                                let uu___190_5826 = g in
                                let uu____5827 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p in
                                {
                                  FStar_Tactics_Types.context = uu____5827;
                                  FStar_Tactics_Types.witness =
                                    (uu___190_5826.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___190_5826.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___190_5826.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___190_5826.FStar_Tactics_Types.is_guard)
                                } in
                              let g2 =
                                let uu___191_5829 = g in
                                let uu____5830 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q in
                                {
                                  FStar_Tactics_Types.context = uu____5830;
                                  FStar_Tactics_Types.witness =
                                    (uu___191_5829.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___191_5829.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___191_5829.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___191_5829.FStar_Tactics_Types.is_guard)
                                } in
                              bind dismiss
                                (fun uu____5837  ->
                                   let uu____5838 = add_goals [g1; g2] in
                                   bind uu____5838
                                     (fun uu____5847  ->
                                        let uu____5848 =
                                          let uu____5853 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p in
                                          let uu____5854 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q in
                                          (uu____5853, uu____5854) in
                                        ret uu____5848))
                          | uu____5859 ->
                              let uu____5872 =
                                FStar_TypeChecker_Normalize.term_to_string
                                  g.FStar_Tactics_Types.context typ in
                              fail1 "Not a disjunction: %s" uu____5872)))) in
    FStar_All.pipe_left (wrap_err "cases") uu____5644
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5911 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5911);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___192_5918 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___192_5918.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___192_5918.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___192_5918.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___192_5918.FStar_Tactics_Types.is_guard)
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
      let uu____5956 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty in
             let uu____5964 = __tc env tm in
             bind uu____5964
               (fun uu____5984  ->
                  match uu____5984 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1))) in
      FStar_All.pipe_left (wrap_err "unquote") uu____5956
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____6017 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6023 =
              let uu____6024 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6024 in
            new_uvar "uvar_env.2" env uu____6023 in
      bind uu____6017
        (fun typ  ->
           let uu____6036 = new_uvar "uvar_env" env typ in
           bind uu____6036 (fun t  -> ret t))
let unshelve: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____6049 =
      bind cur_goal
        (fun goal  ->
           let uu____6055 = __tc goal.FStar_Tactics_Types.context t in
           bind uu____6055
             (fun uu____6075  ->
                match uu____6075 with
                | (t1,typ,guard) ->
                    let uu____6087 =
                      must_trivial goal.FStar_Tactics_Types.context guard in
                    bind uu____6087
                      (fun uu____6092  ->
                         let uu____6093 =
                           let uu____6096 =
                             let uu___193_6097 = goal in
                             let uu____6098 =
                               bnorm goal.FStar_Tactics_Types.context t1 in
                             let uu____6099 =
                               bnorm goal.FStar_Tactics_Types.context typ in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___193_6097.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6098;
                               FStar_Tactics_Types.goal_ty = uu____6099;
                               FStar_Tactics_Types.opts =
                                 (uu___193_6097.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             } in
                           [uu____6096] in
                         add_goals uu____6093))) in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6049
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6119 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____6119)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6139  ->
             let uu____6140 = FStar_Options.unsafe_tactic_exec () in
             if uu____6140
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6146  -> fun uu____6147  -> false) in
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
      let uu____6169 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____6169 with
      | (u,uu____6187,g_u) ->
          let g =
            let uu____6202 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6202;
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
      let uu____6219 = goal_of_goal_ty env typ in
      match uu____6219 with
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