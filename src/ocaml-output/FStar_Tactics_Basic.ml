open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
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
exception TacFailure of Prims.string
let uu___is_TacFailure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | TacFailure uu____32 -> true | uu____33 -> false
let __proj__TacFailure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | TacFailure uu____41 -> uu____41
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result;}
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
  'Auu____105 .
    'Auu____105 tac ->
      FStar_Tactics_Types.proofstate ->
        'Auu____105 FStar_Tactics_Result.__result
  = fun t  -> fun p  -> t.tac_f p
let ret: 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p))
let bind: 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____172 = run t1 p in
           match uu____172 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____179 = t2 a in run uu____179 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: FStar_Tactics_Types.goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____191 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____191
        (FStar_Syntax_Print.binders_to_string ", ") in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
    let uu____194 =
      FStar_TypeChecker_Normalize.term_to_string
        g.FStar_Tactics_Types.context w in
    let uu____195 =
      FStar_TypeChecker_Normalize.term_to_string
        g.FStar_Tactics_Types.context t in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____194 uu____195
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____208 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____208
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____221 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____221
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____238 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____238
let comp_to_typ: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____244) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____254) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: FStar_Tactics_Types.goal -> Prims.bool =
  fun g  ->
    let uu____268 =
      let uu____273 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty in
      FStar_Syntax_Util.un_squash uu____273 in
    match uu____268 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____279 -> false
let dump_goal:
  'Auu____290 . 'Auu____290 -> FStar_Tactics_Types.goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____300 = goal_to_string goal in tacprint uu____300
let dump_cur: FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____310 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____314 = FStar_List.hd ps.FStar_Tactics_Types.goals in
            dump_goal ps uu____314))
let ps_to_string:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu____322  ->
    match uu____322 with
    | (msg,ps) ->
        let uu____329 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.goals) in
        let uu____330 =
          let uu____331 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.goals in
          FStar_String.concat "\n" uu____331 in
        let uu____334 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.smt_goals) in
        let uu____335 =
          let uu____336 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.smt_goals in
          FStar_String.concat "\n" uu____336 in
        FStar_Util.format5
          "State dump (%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s" msg
          uu____329 uu____330 uu____334 uu____335
let goal_to_json: FStar_Tactics_Types.goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____344 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____344 FStar_Syntax_Print.binders_to_json in
    let uu____345 =
      let uu____352 =
        let uu____359 =
          let uu____364 =
            let uu____365 =
              let uu____372 =
                let uu____377 =
                  let uu____378 =
                    FStar_TypeChecker_Normalize.term_to_string
                      g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness in
                  FStar_Util.JsonStr uu____378 in
                ("witness", uu____377) in
              let uu____379 =
                let uu____386 =
                  let uu____391 =
                    let uu____392 =
                      FStar_TypeChecker_Normalize.term_to_string
                        g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty in
                    FStar_Util.JsonStr uu____392 in
                  ("type", uu____391) in
                [uu____386] in
              uu____372 :: uu____379 in
            FStar_Util.JsonAssoc uu____365 in
          ("goal", uu____364) in
        [uu____359] in
      ("hyps", g_binders) :: uu____352 in
    FStar_Util.JsonAssoc uu____345
let ps_to_json:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____424  ->
    match uu____424 with
    | (msg,ps) ->
        let uu____431 =
          let uu____438 =
            let uu____445 =
              let uu____450 =
                let uu____451 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals in
                FStar_Util.JsonList uu____451 in
              ("goals", uu____450) in
            let uu____454 =
              let uu____461 =
                let uu____466 =
                  let uu____467 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals in
                  FStar_Util.JsonList uu____467 in
                ("smt-goals", uu____466) in
              [uu____461] in
            uu____445 :: uu____454 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____438 in
        FStar_Util.JsonAssoc uu____431
let dump_proofstate:
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____496  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
let print_proof_state1: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac (fun p  -> dump_cur p msg; FStar_Tactics_Result.Success ((), p))
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac
      (fun p  -> dump_proofstate p msg; FStar_Tactics_Result.Success ((), p))
let get: FStar_Tactics_Types.proofstate tac =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p))
let tac_verb_dbg: Prims.bool FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let rec log:
  FStar_Tactics_Types.proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit
  =
  fun ps  ->
    fun f  ->
      let uu____556 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____556 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____578 =
              let uu____581 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____581 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____578);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail: 'Auu____621 . Prims.string -> 'Auu____621 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____632 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____632
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____640 . Prims.string -> Prims.string -> 'Auu____640 tac =
  fun msg  ->
    fun x  -> let uu____651 = FStar_Util.format1 msg x in fail uu____651
let fail2:
  'Auu____660 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____660 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____675 = FStar_Util.format2 msg x y in fail uu____675
let fail3:
  'Auu____686 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____686 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____705 = FStar_Util.format3 msg x y z in fail uu____705
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____733 = run t ps in
         match uu____733 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success
                ((FStar_Pervasives_Native.Some a), q))
         | FStar_Tactics_Result.Failed (uu____747,uu____748) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____763  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____781 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____795 =
         let uu___90_796 = p in
         let uu____797 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___90_796.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___90_796.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___90_796.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____797;
           FStar_Tactics_Types.smt_goals =
             (uu___90_796.FStar_Tactics_Types.smt_goals)
         } in
       set uu____795)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____812 = trysolve goal solution in
      if uu____812
      then dismiss
      else
        (let uu____816 =
           let uu____817 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____818 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____819 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____817 uu____818
             uu____819 in
         fail uu____816)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___91_826 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___91_826.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___91_826.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___91_826.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___91_826.FStar_Tactics_Types.smt_goals)
          }))
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___92_843 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___92_843.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___92_843.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___92_843.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___92_843.FStar_Tactics_Types.smt_goals)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___93_860 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___93_860.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___93_860.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___93_860.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___93_860.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___94_877 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___94_877.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___94_877.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___94_877.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___94_877.FStar_Tactics_Types.smt_goals)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___95_894 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___95_894.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___95_894.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___95_894.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___95_894.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____904  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___96_917 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___96_917.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___96_917.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___96_917.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___96_917.FStar_Tactics_Types.smt_goals)
            }))
let new_uvar: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun typ  ->
      let uu____942 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____942 with
      | (u,uu____958,g_u) ->
          let uu____972 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____972 (fun uu____976  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____981 = FStar_Syntax_Util.un_squash t in
    match uu____981 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____991 =
          let uu____992 = FStar_Syntax_Subst.compress t' in
          uu____992.FStar_Syntax_Syntax.n in
        (match uu____991 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____996 -> false)
    | uu____997 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1006 = FStar_Syntax_Util.un_squash t in
    match uu____1006 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1016 =
          let uu____1017 = FStar_Syntax_Subst.compress t' in
          uu____1017.FStar_Syntax_Syntax.n in
        (match uu____1016 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1021 -> false)
    | uu____1022 -> false
let cur_goal: FStar_Tactics_Types.goal tac =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let mk_irrelevant_goal:
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Options.optionstate -> FStar_Tactics_Types.goal tac
  =
  fun env  ->
    fun phi  ->
      fun opts  ->
        let typ = FStar_Syntax_Util.mk_squash phi in
        let uu____1056 = new_uvar env typ in
        bind uu____1056
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
let add_irrelevant_goal:
  env ->
    FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun env  ->
    fun phi  ->
      fun opts  ->
        let uu____1079 = mk_irrelevant_goal env phi opts in
        bind uu____1079 (fun goal  -> add_goals [goal])
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
       let uu____1101 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1101
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1105 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1105))
let add_goal_from_guard:
  env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Options.optionstate -> Prims.unit tac
  =
  fun e  ->
    fun g  ->
      fun opts  ->
        let uu____1122 =
          let uu____1123 = FStar_TypeChecker_Rel.simplify_guard e g in
          uu____1123.FStar_TypeChecker_Env.guard_f in
        match uu____1122 with
        | FStar_TypeChecker_Common.Trivial  -> ret ()
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____1127 = istrivial e f in
            if uu____1127
            then ret ()
            else
              (let uu____1131 = mk_irrelevant_goal e f opts in
               bind uu____1131
                 (fun goal  ->
                    let goal1 =
                      let uu___97_1138 = goal in
                      {
                        FStar_Tactics_Types.context =
                          (uu___97_1138.FStar_Tactics_Types.context);
                        FStar_Tactics_Types.witness =
                          (uu___97_1138.FStar_Tactics_Types.witness);
                        FStar_Tactics_Types.goal_ty =
                          (uu___97_1138.FStar_Tactics_Types.goal_ty);
                        FStar_Tactics_Types.opts =
                          (uu___97_1138.FStar_Tactics_Types.opts);
                        FStar_Tactics_Types.is_guard = true
                      } in
                    push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1144 = is_irrelevant g in
       if uu____1144
       then bind dismiss (fun uu____1148  -> add_smt_goals [g])
       else
         (let uu____1150 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1150))
let divide:
  'a 'b .
    Prims.int ->
      'a tac -> 'b tac -> ('a,'b) FStar_Pervasives_Native.tuple2 tac
  =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____1196 =
               try
                 let uu____1230 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1230
               with | uu____1260 -> fail "divide: not enough goals" in
             bind uu____1196
               (fun uu____1287  ->
                  match uu____1287 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___98_1313 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___98_1313.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___98_1313.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___98_1313.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = []
                        } in
                      let rp =
                        let uu___99_1315 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___99_1315.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___99_1315.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___99_1315.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = []
                        } in
                      let uu____1316 = set lp in
                      bind uu____1316
                        (fun uu____1324  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1338 = set rp in
                                     bind uu____1338
                                       (fun uu____1346  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___100_1362 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___100_1362.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___100_1362.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___100_1362.FStar_Tactics_Types.all_implicits);
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
                                                                p.FStar_Tactics_Types.smt_goals))
                                                      } in
                                                    let uu____1363 = set p' in
                                                    bind uu____1363
                                                      (fun uu____1371  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1391 = divide (Prims.parse_int "1") f idtac in
    bind uu____1391
      (fun uu____1404  -> match uu____1404 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1439::uu____1440 ->
             let uu____1443 =
               let uu____1452 = map tau in
               divide (Prims.parse_int "1") tau uu____1452 in
             bind uu____1443
               (fun uu____1470  ->
                  match uu____1470 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1509 =
        bind t1
          (fun uu____1514  ->
             let uu____1515 = map t2 in
             bind uu____1515 (fun uu____1523  -> ret ())) in
      focus uu____1509
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1534 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1534 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1549 =
             let uu____1550 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1550 in
           if uu____1549
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1556 = new_uvar env' typ' in
              bind uu____1556
                (fun u  ->
                   let uu____1563 =
                     let uu____1564 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1564 in
                   if uu____1563
                   then
                     let uu____1567 =
                       let uu____1570 =
                         let uu___103_1571 = goal in
                         let uu____1572 = bnorm env' u in
                         let uu____1573 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1572;
                           FStar_Tactics_Types.goal_ty = uu____1573;
                           FStar_Tactics_Types.opts =
                             (uu___103_1571.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___103_1571.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1570 in
                     bind uu____1567 (fun uu____1575  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1581 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1581)
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
       (let uu____1602 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1602 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1621 =
              let uu____1622 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1622 in
            if uu____1621
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1638 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1638; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1640 =
                 let uu____1643 = comp_to_typ c in new_uvar env' uu____1643 in
               bind uu____1640
                 (fun u  ->
                    let lb =
                      let uu____1659 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____1659 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1663 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1663 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____1700 =
                            let uu____1703 =
                              let uu___104_1704 = goal in
                              let uu____1705 = bnorm env' u in
                              let uu____1706 =
                                let uu____1707 = comp_to_typ c in
                                bnorm env' uu____1707 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____1705;
                                FStar_Tactics_Types.goal_ty = uu____1706;
                                FStar_Tactics_Types.opts =
                                  (uu___104_1704.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___104_1704.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____1703 in
                          bind uu____1700
                            (fun uu____1714  ->
                               let uu____1715 =
                                 let uu____1720 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____1720, b) in
                               ret uu____1715)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____1734 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1734))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____1759 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1759 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___105_1766 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___105_1766.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___105_1766.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___105_1766.FStar_Tactics_Types.is_guard)
            }))
let norm_term:
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun s  ->
    fun t  ->
      bind get
        (fun ps  ->
           let steps =
             let uu____1790 = FStar_TypeChecker_Normalize.tr_norm_steps s in
             FStar_List.append
               [FStar_TypeChecker_Normalize.Reify;
               FStar_TypeChecker_Normalize.UnfoldTac] uu____1790 in
           let t1 = normalize steps ps.FStar_Tactics_Types.main_context t in
           ret t1)
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1805 =
           try
             let uu____1833 =
               (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
                 goal.FStar_Tactics_Types.context t in
             ret uu____1833
           with
           | e ->
               let uu____1860 = FStar_Syntax_Print.term_to_string t in
               let uu____1861 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1860
                 uu____1861 in
         bind uu____1805
           (fun uu____1879  ->
              match uu____1879 with
              | (t1,typ,guard) ->
                  let uu____1891 =
                    let uu____1892 =
                      let uu____1893 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1893 in
                    Prims.op_Negation uu____1892 in
                  if uu____1891
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1897 =
                       do_unify goal.FStar_Tactics_Types.context typ
                         goal.FStar_Tactics_Types.goal_ty in
                     if uu____1897
                     then solve goal t1
                     else
                       (let uu____1901 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context t1 in
                        let uu____1902 =
                          let uu____1903 =
                            bnorm goal.FStar_Tactics_Types.context typ in
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context uu____1903 in
                        let uu____1904 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context
                            goal.FStar_Tactics_Types.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1901 uu____1902 uu____1904))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  -> let uu____1913 = __exact t in focus uu____1913
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1927 =
           try
             let uu____1955 =
               FStar_TypeChecker_TcTerm.tc_term
                 goal.FStar_Tactics_Types.context t in
             ret uu____1955
           with
           | e ->
               let uu____1982 = FStar_Syntax_Print.term_to_string t in
               let uu____1983 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1982
                 uu____1983 in
         bind uu____1927
           (fun uu____2001  ->
              match uu____2001 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2019 =
                       let uu____2020 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2020 in
                     if uu____2019
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2024 =
                          let uu____2033 =
                            let uu____2042 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2042.FStar_Syntax_Syntax.effect_args in
                          match uu____2033 with
                          | pre::post::uu____2053 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2094 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2024 with
                        | (pre,post) ->
                            let uu____2123 =
                              do_unify goal.FStar_Tactics_Types.context post
                                goal.FStar_Tactics_Types.goal_ty in
                            if uu____2123
                            then
                              let uu____2126 = solve goal t1 in
                              bind uu____2126
                                (fun uu____2130  ->
                                   add_irrelevant_goal
                                     goal.FStar_Tactics_Types.context pre
                                     goal.FStar_Tactics_Types.opts)
                            else
                              (let uu____2132 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context t1 in
                               let uu____2133 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context post in
                               let uu____2134 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2132 uu____2133 uu____2134)))))
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2147 =
             let uu____2154 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2154 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2147 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2181 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2201 =
               let uu____2206 = __exact tm in trytac uu____2206 in
             bind uu____2201
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2219 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2219 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           let uu____2249 =
                             let uu____2250 =
                               FStar_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu____2250 in
                           if uu____2249
                           then fail "apply: not total codomain"
                           else
                             (let uu____2254 =
                                new_uvar goal.FStar_Tactics_Types.context
                                  bv.FStar_Syntax_Syntax.sort in
                              bind uu____2254
                                (fun u  ->
                                   let tm' =
                                     FStar_Syntax_Syntax.mk_Tm_app tm
                                       [(u, aq)] FStar_Pervasives_Native.None
                                       (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                   let typ' =
                                     let uu____2274 = comp_to_typ c in
                                     FStar_All.pipe_left
                                       (FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.NT (bv, u)])
                                       uu____2274 in
                                   let uu____2275 = __apply uopt tm' typ' in
                                   bind uu____2275
                                     (fun uu____2283  ->
                                        let u1 =
                                          bnorm
                                            goal.FStar_Tactics_Types.context
                                            u in
                                        let uu____2285 =
                                          let uu____2286 =
                                            let uu____2289 =
                                              let uu____2290 =
                                                FStar_Syntax_Util.head_and_args
                                                  u1 in
                                              FStar_Pervasives_Native.fst
                                                uu____2290 in
                                            FStar_Syntax_Subst.compress
                                              uu____2289 in
                                          uu____2286.FStar_Syntax_Syntax.n in
                                        match uu____2285 with
                                        | FStar_Syntax_Syntax.Tm_uvar
                                            (uvar,uu____2318) ->
                                            bind get
                                              (fun ps  ->
                                                 let uu____2346 =
                                                   uopt &&
                                                     (uvar_free uvar ps) in
                                                 if uu____2346
                                                 then ret ()
                                                 else
                                                   (let uu____2350 =
                                                      let uu____2353 =
                                                        let uu___110_2354 =
                                                          goal in
                                                        let uu____2355 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            u1 in
                                                        let uu____2356 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          FStar_Tactics_Types.context
                                                            =
                                                            (uu___110_2354.FStar_Tactics_Types.context);
                                                          FStar_Tactics_Types.witness
                                                            = uu____2355;
                                                          FStar_Tactics_Types.goal_ty
                                                            = uu____2356;
                                                          FStar_Tactics_Types.opts
                                                            =
                                                            (uu___110_2354.FStar_Tactics_Types.opts);
                                                          FStar_Tactics_Types.is_guard
                                                            = false
                                                        } in
                                                      [uu____2353] in
                                                    add_goals uu____2350))
                                        | t -> ret ()))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2415 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2415 with
           | (tm1,typ,guard) ->
               let uu____2427 =
                 let uu____2430 =
                   let uu____2433 = __apply uopt tm1 typ in
                   bind uu____2433
                     (fun uu____2437  ->
                        add_goal_from_guard goal.FStar_Tactics_Types.context
                          guard goal.FStar_Tactics_Types.opts) in
                 focus uu____2430 in
               let uu____2438 =
                 let uu____2441 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context tm1 in
                 let uu____2442 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context typ in
                 let uu____2443 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context
                     goal.FStar_Tactics_Types.goal_ty in
                 fail3
                   "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                   uu____2441 uu____2442 uu____2443 in
               try_unif uu____2427 uu____2438)
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2452 =
      let is_unit_t t =
        let uu____2459 =
          let uu____2460 = FStar_Syntax_Subst.compress t in
          uu____2460.FStar_Syntax_Syntax.n in
        match uu____2459 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
            true
        | uu____2464 -> false in
      bind cur_goal
        (fun goal  ->
           let uu____2474 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2474 with
           | (tm1,t,guard) ->
               let uu____2486 = FStar_Syntax_Util.arrow_formals_comp t in
               (match uu____2486 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2516 =
                         FStar_List.fold_left
                           (fun uu____2562  ->
                              fun uu____2563  ->
                                match (uu____2562, uu____2563) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2666 = is_unit_t b_t in
                                    if uu____2666
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____2704 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.FStar_Tactics_Types.context
                                           b_t in
                                       match uu____2704 with
                                       | (u,uu____2734,g_u) ->
                                           let uu____2748 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____2748,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2516 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____2818 =
                             let uu____2827 =
                               let uu____2836 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____2836.FStar_Syntax_Syntax.effect_args in
                             match uu____2827 with
                             | pre::post::uu____2847 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____2888 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____2818 with
                            | (pre,post) ->
                                let uu____2917 =
                                  let uu____2918 =
                                    let uu____2919 =
                                      FStar_Syntax_Util.mk_squash post in
                                    do_unify goal.FStar_Tactics_Types.context
                                      uu____2919
                                      goal.FStar_Tactics_Types.goal_ty in
                                  Prims.op_Negation uu____2918 in
                                if uu____2917
                                then
                                  let uu____2922 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context tm1 in
                                  let uu____2923 =
                                    let uu____2924 =
                                      FStar_Syntax_Util.mk_squash post in
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context
                                      uu____2924 in
                                  let uu____2925 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context
                                      goal.FStar_Tactics_Types.goal_ty in
                                  fail3
                                    "apply_lemma: Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                    uu____2922 uu____2923 uu____2925
                                else
                                  (let solution =
                                     let uu____2928 =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       goal.FStar_Tactics_Types.context
                                       uu____2928 in
                                   let implicits1 =
                                     FStar_All.pipe_right
                                       implicits.FStar_TypeChecker_Env.implicits
                                       (FStar_List.filter
                                          (fun uu____2996  ->
                                             match uu____2996 with
                                             | (uu____3009,uu____3010,uu____3011,tm2,uu____3013,uu____3014)
                                                 ->
                                                 let uu____3015 =
                                                   FStar_Syntax_Util.head_and_args
                                                     tm2 in
                                                 (match uu____3015 with
                                                  | (hd1,uu____3031) ->
                                                      let uu____3052 =
                                                        let uu____3053 =
                                                          FStar_Syntax_Subst.compress
                                                            hd1 in
                                                        uu____3053.FStar_Syntax_Syntax.n in
                                                      (match uu____3052 with
                                                       | FStar_Syntax_Syntax.Tm_uvar
                                                           uu____3056 -> true
                                                       | uu____3073 -> false)))) in
                                   let uu____3074 = solve goal solution in
                                   bind uu____3074
                                     (fun uu____3079  ->
                                        let uu____3080 =
                                          add_implicits implicits1 in
                                        bind uu____3080
                                          (fun uu____3091  ->
                                             let is_free_uvar uv t1 =
                                               let free_uvars =
                                                 let uu____3102 =
                                                   let uu____3109 =
                                                     FStar_Syntax_Free.uvars
                                                       t1 in
                                                   FStar_Util.set_elements
                                                     uu____3109 in
                                                 FStar_List.map
                                                   FStar_Pervasives_Native.fst
                                                   uu____3102 in
                                               FStar_List.existsML
                                                 (fun u  ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      u uv) free_uvars in
                                             let appears uv goals =
                                               FStar_List.existsML
                                                 (fun g'  ->
                                                    is_free_uvar uv
                                                      g'.FStar_Tactics_Types.goal_ty)
                                                 goals in
                                             let checkone t1 goals =
                                               let uu____3150 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t1 in
                                               match uu____3150 with
                                               | (hd1,uu____3166) ->
                                                   (match hd1.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_uvar
                                                        (uv,uu____3188) ->
                                                        appears uv goals
                                                    | uu____3213 -> false) in
                                             let sub_goals =
                                               FStar_All.pipe_right
                                                 implicits1
                                                 (FStar_List.map
                                                    (fun uu____3255  ->
                                                       match uu____3255 with
                                                       | (_msg,_env,_uvar,term,typ,uu____3273)
                                                           ->
                                                           let uu___113_3274
                                                             = goal in
                                                           let uu____3275 =
                                                             bnorm
                                                               goal.FStar_Tactics_Types.context
                                                               term in
                                                           let uu____3276 =
                                                             bnorm
                                                               goal.FStar_Tactics_Types.context
                                                               typ in
                                                           {
                                                             FStar_Tactics_Types.context
                                                               =
                                                               (uu___113_3274.FStar_Tactics_Types.context);
                                                             FStar_Tactics_Types.witness
                                                               = uu____3275;
                                                             FStar_Tactics_Types.goal_ty
                                                               = uu____3276;
                                                             FStar_Tactics_Types.opts
                                                               =
                                                               (uu___113_3274.FStar_Tactics_Types.opts);
                                                             FStar_Tactics_Types.is_guard
                                                               =
                                                               (uu___113_3274.FStar_Tactics_Types.is_guard)
                                                           })) in
                                             let rec filter' f xs =
                                               match xs with
                                               | [] -> []
                                               | x::xs1 ->
                                                   let uu____3314 = f x xs1 in
                                                   if uu____3314
                                                   then
                                                     let uu____3317 =
                                                       filter' f xs1 in
                                                     x :: uu____3317
                                                   else filter' f xs1 in
                                             let sub_goals1 =
                                               filter'
                                                 (fun g  ->
                                                    fun goals  ->
                                                      let uu____3331 =
                                                        checkone
                                                          g.FStar_Tactics_Types.witness
                                                          goals in
                                                      Prims.op_Negation
                                                        uu____3331) sub_goals in
                                             let uu____3332 =
                                               add_goal_from_guard
                                                 goal.FStar_Tactics_Types.context
                                                 guard
                                                 goal.FStar_Tactics_Types.opts in
                                             bind uu____3332
                                               (fun uu____3337  ->
                                                  let uu____3338 =
                                                    let uu____3341 =
                                                      let uu____3342 =
                                                        let uu____3343 =
                                                          FStar_Syntax_Util.mk_squash
                                                            pre in
                                                        istrivial
                                                          goal.FStar_Tactics_Types.context
                                                          uu____3343 in
                                                      Prims.op_Negation
                                                        uu____3342 in
                                                    if uu____3341
                                                    then
                                                      add_irrelevant_goal
                                                        goal.FStar_Tactics_Types.context
                                                        pre
                                                        goal.FStar_Tactics_Types.opts
                                                    else ret () in
                                                  bind uu____3338
                                                    (fun uu____3348  ->
                                                       add_goals sub_goals1))))))))) in
    focus uu____2452
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3365 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3365 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3375::(e1,uu____3377)::(e2,uu____3379)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3438 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3461 = destruct_eq' typ in
    match uu____3461 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3491 = FStar_Syntax_Util.un_squash typ in
        (match uu____3491 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3524 =
           FStar_All.pipe_left mlog
             (fun uu____3534  ->
                let uu____3535 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3536 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3535
                  uu____3536) in
         bind uu____3524
           (fun uu____3544  ->
              let uu____3545 =
                let uu____3552 =
                  let uu____3553 =
                    FStar_TypeChecker_Env.lookup_bv
                      goal.FStar_Tactics_Types.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3553 in
                destruct_eq uu____3552 in
              match uu____3545 with
              | FStar_Pervasives_Native.Some (x,e) ->
                  let uu____3570 =
                    let uu____3571 = FStar_Syntax_Subst.compress x in
                    uu____3571.FStar_Syntax_Syntax.n in
                  (match uu____3570 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___114_3578 = goal in
                         let uu____3579 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)]
                             goal.FStar_Tactics_Types.witness in
                         let uu____3580 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)]
                             goal.FStar_Tactics_Types.goal_ty in
                         {
                           FStar_Tactics_Types.context =
                             (uu___114_3578.FStar_Tactics_Types.context);
                           FStar_Tactics_Types.witness = uu____3579;
                           FStar_Tactics_Types.goal_ty = uu____3580;
                           FStar_Tactics_Types.opts =
                             (uu___114_3578.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___114_3578.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur goal1
                   | uu____3581 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3582 -> fail "Not an equality hypothesis"))
let subst_goal:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal
  =
  fun b1  ->
    fun b2  ->
      fun s  ->
        fun g  ->
          let rec alpha e =
            let uu____3613 = FStar_TypeChecker_Env.pop_bv e in
            match uu____3613 with
            | FStar_Pervasives_Native.None  -> e
            | FStar_Pervasives_Native.Some (bv,e') ->
                if FStar_Syntax_Syntax.bv_eq bv b1
                then FStar_TypeChecker_Env.push_bv e' b2
                else
                  (let uu____3631 = alpha e' in
                   let uu____3632 =
                     let uu___115_3633 = bv in
                     let uu____3634 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___115_3633.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___115_3633.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3634
                     } in
                   FStar_TypeChecker_Env.push_bv uu____3631 uu____3632) in
          let c = alpha g.FStar_Tactics_Types.context in
          let w = FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
          let t = FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
          let uu___116_3640 = g in
          {
            FStar_Tactics_Types.context = c;
            FStar_Tactics_Types.witness = w;
            FStar_Tactics_Types.goal_ty = t;
            FStar_Tactics_Types.opts =
              (uu___116_3640.FStar_Tactics_Types.opts);
            FStar_Tactics_Types.is_guard =
              (uu___116_3640.FStar_Tactics_Types.is_guard)
          }
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3661 = b in
           match uu____3661 with
           | (bv,uu____3665) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___117_3669 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___117_3669.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___117_3669.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3673 =
                   let uu____3674 =
                     let uu____3681 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3681) in
                   FStar_Syntax_Syntax.NT uu____3674 in
                 [uu____3673] in
               let uu____3682 = subst_goal bv bv' s1 goal in
               replace_cur uu____3682)
let rec find_bv_env:
  env ->
    FStar_Syntax_Syntax.bv ->
      (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.universe,
        env,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple6 tac
  =
  fun e  ->
    fun bv  ->
      let uu____3723 = FStar_TypeChecker_Env.pop_bv e in
      match uu____3723 with
      | FStar_Pervasives_Native.None  ->
          fail "binder_retype: binder is not present in environment"
      | FStar_Pervasives_Native.Some (bv',e') ->
          if FStar_Syntax_Syntax.bv_eq bv bv'
          then
            let uu____3786 =
              let uu____3793 = FStar_Syntax_Util.type_u () in
              match uu____3793 with | (ty,u) -> ret (ty, u) in
            bind uu____3786
              (fun uu____3832  ->
                 match uu____3832 with
                 | (ty,u) ->
                     let uu____3855 = new_uvar e' ty in
                     bind uu____3855
                       (fun t'  ->
                          let bv'' =
                            let uu___118_3877 = bv in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___118_3877.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___118_3877.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t'
                            } in
                          let uu____3878 =
                            let uu____3893 =
                              FStar_TypeChecker_Env.push_bv e' bv'' in
                            let uu____3894 =
                              let uu____3897 =
                                let uu____3898 =
                                  let uu____3905 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____3905) in
                                FStar_Syntax_Syntax.NT uu____3898 in
                              [uu____3897] in
                            (e', ty, t', u, uu____3893, uu____3894) in
                          ret uu____3878))
          else
            (let uu____3923 = find_bv_env e' bv in
             bind uu____3923
               (fun uu____3977  ->
                  match uu____3977 with
                  | (e1,ty,t,u,e2,s) ->
                      let bv'1 =
                        let uu___119_4019 = bv' in
                        let uu____4020 =
                          FStar_Syntax_Subst.subst s
                            bv'.FStar_Syntax_Syntax.sort in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___119_4019.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___119_4019.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = uu____4020
                        } in
                      let uu____4023 =
                        let uu____4038 =
                          FStar_TypeChecker_Env.push_bv e2 bv'1 in
                        (e1, ty, t, u, uu____4038, s) in
                      ret uu____4023))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4068 = b in
         match uu____4068 with
         | (bv,uu____4072) ->
             bind dismiss
               (fun uu____4075  ->
                  let uu____4076 =
                    find_bv_env goal.FStar_Tactics_Types.context bv in
                  bind uu____4076
                    (fun uu____4115  ->
                       match uu____4115 with
                       | (env',ty,t',u,env,s) ->
                           let uu____4142 =
                             let uu____4145 =
                               let uu____4148 =
                                 let uu___120_4149 = goal in
                                 let uu____4150 =
                                   FStar_Syntax_Subst.subst s
                                     goal.FStar_Tactics_Types.witness in
                                 let uu____4151 =
                                   FStar_Syntax_Subst.subst s
                                     goal.FStar_Tactics_Types.goal_ty in
                                 {
                                   FStar_Tactics_Types.context = env;
                                   FStar_Tactics_Types.witness = uu____4150;
                                   FStar_Tactics_Types.goal_ty = uu____4151;
                                   FStar_Tactics_Types.opts =
                                     (uu___120_4149.FStar_Tactics_Types.opts);
                                   FStar_Tactics_Types.is_guard =
                                     (uu___120_4149.FStar_Tactics_Types.is_guard)
                                 } in
                               [uu____4148] in
                             add_goals uu____4145 in
                           bind uu____4142
                             (fun uu____4154  ->
                                let uu____4155 =
                                  FStar_Syntax_Util.mk_eq2
                                    (FStar_Syntax_Syntax.U_succ u) ty
                                    bv.FStar_Syntax_Syntax.sort t' in
                                add_irrelevant_goal env' uu____4155
                                  goal.FStar_Tactics_Types.opts))))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4161 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4161 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4183 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4183 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___121_4217 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___121_4217.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___121_4217.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4229 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4229 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4250 = FStar_Syntax_Print.bv_to_string x in
               let uu____4251 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4250 uu____4251
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4258 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4258 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4280 = FStar_Util.set_mem x fns_ty in
           if uu____4280
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4284 = new_uvar env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4284
                (fun u  ->
                   let uu____4290 =
                     let uu____4291 = trysolve goal u in
                     Prims.op_Negation uu____4291 in
                   if uu____4290
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___122_4296 = goal in
                        let uu____4297 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4297;
                          FStar_Tactics_Types.goal_ty =
                            (uu___122_4296.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___122_4296.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___122_4296.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4299  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4311 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4311 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4335  ->
                    let uu____4336 = clear b in
                    bind uu____4336
                      (fun uu____4340  ->
                         bind intro (fun uu____4342  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___123_4359 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___123_4359.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___123_4359.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___123_4359.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___123_4359.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4361  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___124_4378 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___124_4378.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___124_4378.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___124_4378.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___124_4378.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4380  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4422 = f x in
          bind uu____4422
            (fun y  ->
               let uu____4430 = mapM f xs in
               bind uu____4430 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4476 = FStar_Syntax_Subst.compress t in
          uu____4476.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4511 = ff hd1 in
              bind uu____4511
                (fun hd2  ->
                   let fa uu____4531 =
                     match uu____4531 with
                     | (a,q) ->
                         let uu____4544 = ff a in
                         bind uu____4544 (fun a1  -> ret (a1, q)) in
                   let uu____4557 = mapM fa args in
                   bind uu____4557
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4617 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4617 with
               | (bs1,t') ->
                   let uu____4626 =
                     let uu____4629 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4629 t' in
                   bind uu____4626
                     (fun t''  ->
                        let uu____4633 =
                          let uu____4634 =
                            let uu____4651 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4652 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4651, uu____4652, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4634 in
                        ret uu____4633))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4673 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___125_4677 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___125_4677.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___125_4677.FStar_Syntax_Syntax.vars)
                }))
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
            let uu____4706 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4706 with
            | (t1,lcomp,g) ->
                let uu____4718 =
                  (let uu____4721 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____4721) ||
                    (let uu____4723 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4723) in
                if uu____4718
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4730 = new_uvar env typ in
                   bind uu____4730
                     (fun ut  ->
                        log ps
                          (fun uu____4741  ->
                             let uu____4742 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4743 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4742 uu____4743);
                        (let uu____4744 =
                           let uu____4747 =
                             let uu____4748 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4748 typ t1 ut in
                           add_irrelevant_goal env uu____4747 opts in
                         bind uu____4744
                           (fun uu____4751  ->
                              let uu____4752 =
                                bind tau
                                  (fun uu____4757  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4752))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4778 =
           match ps.FStar_Tactics_Types.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4778 with
         | (g,gs) ->
             let gt1 = g.FStar_Tactics_Types.goal_ty in
             (log ps
                (fun uu____4815  ->
                   let uu____4816 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4816);
              bind dismiss_all
                (fun uu____4819  ->
                   let uu____4820 =
                     tac_bottom_fold_env
                       (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                       g.FStar_Tactics_Types.context gt1 in
                   bind uu____4820
                     (fun gt'  ->
                        log ps
                          (fun uu____4830  ->
                             let uu____4831 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4831);
                        (let uu____4832 = push_goals gs in
                         bind uu____4832
                           (fun uu____4836  ->
                              add_goals
                                [(let uu___126_4838 = g in
                                  {
                                    FStar_Tactics_Types.context =
                                      (uu___126_4838.FStar_Tactics_Types.context);
                                    FStar_Tactics_Types.witness =
                                      (uu___126_4838.FStar_Tactics_Types.witness);
                                    FStar_Tactics_Types.goal_ty = gt';
                                    FStar_Tactics_Types.opts =
                                      (uu___126_4838.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___126_4838.FStar_Tactics_Types.is_guard)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4858 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____4858 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4870 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4870 with
            | (hd1,args) ->
                let uu____4903 =
                  let uu____4916 =
                    let uu____4917 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4917.FStar_Syntax_Syntax.n in
                  (uu____4916, args) in
                (match uu____4903 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4931::(l,uu____4933)::(r,uu____4935)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4982 =
                       let uu____4983 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____4983 in
                     if uu____4982
                     then
                       let uu____4986 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____4987 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4986 uu____4987
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____4990) ->
                     let uu____5007 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____5007))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5015 =
         new_uvar g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
       bind uu____5015
         (fun u  ->
            let g' =
              let uu___127_5022 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___127_5022.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___127_5022.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___127_5022.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___127_5022.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____5025  ->
                 let uu____5026 =
                   let uu____5029 =
                     let uu____5030 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____5030
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal g.FStar_Tactics_Types.context
                     uu____5029 g.FStar_Tactics_Types.opts in
                 bind uu____5026
                   (fun uu____5033  ->
                      let uu____5034 = add_goals [g'] in
                      bind uu____5034 (fun uu____5038  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___128_5055 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___128_5055.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___128_5055.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___128_5055.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___128_5055.FStar_Tactics_Types.smt_goals)
              })
       | uu____5056 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___129_5071 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___129_5071.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___129_5071.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___129_5071.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___129_5071.FStar_Tactics_Types.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5078 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____5120 =
           (g.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
             g.FStar_Tactics_Types.context t in
         match uu____5120 with
         | (t1,typ,guard) ->
             let uu____5136 = FStar_Syntax_Util.head_and_args typ in
             (match uu____5136 with
              | (hd1,args) ->
                  let uu____5179 =
                    let uu____5192 =
                      let uu____5193 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____5193.FStar_Syntax_Syntax.n in
                    (uu____5192, args) in
                  (match uu____5179 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____5212)::(q,uu____5214)::[]) when
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
                         let uu___130_5252 = g in
                         let uu____5253 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_p in
                         {
                           FStar_Tactics_Types.context = uu____5253;
                           FStar_Tactics_Types.witness =
                             (uu___130_5252.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___130_5252.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___130_5252.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___130_5252.FStar_Tactics_Types.is_guard)
                         } in
                       let g2 =
                         let uu___131_5255 = g in
                         let uu____5256 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_q in
                         {
                           FStar_Tactics_Types.context = uu____5256;
                           FStar_Tactics_Types.witness =
                             (uu___131_5255.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___131_5255.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___131_5255.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___131_5255.FStar_Tactics_Types.is_guard)
                         } in
                       bind dismiss
                         (fun uu____5263  ->
                            let uu____5264 = add_goals [g1; g2] in
                            bind uu____5264
                              (fun uu____5273  ->
                                 let uu____5274 =
                                   let uu____5279 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____5280 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____5279, uu____5280) in
                                 ret uu____5274))
                   | uu____5285 ->
                       let uu____5298 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context typ in
                       fail1 "Not a disjunction: %s" uu____5298)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5321 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5321);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___132_5328 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___132_5328.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___132_5328.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___132_5328.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___132_5328.FStar_Tactics_Types.is_guard)
                 } in
               replace_cur g'
           | FStar_Getopt.Error err1 ->
               fail2 "Setting options `%s` failed: %s" s err1
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
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
      bind cur_goal
        (fun goal  ->
           let env =
             FStar_TypeChecker_Env.set_expected_typ
               goal.FStar_Tactics_Types.context ty in
           let uu____5369 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               env tm in
           match uu____5369 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5398 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5404 =
              let uu____5405 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5405 in
            new_uvar env uu____5404 in
      bind uu____5398
        (fun typ  ->
           let uu____5417 = new_uvar env typ in
           bind uu____5417 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5437 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5437)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5457  ->
             let uu____5458 = FStar_Options.unsafe_tactic_exec () in
             if uu____5458
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5464  -> fun uu____5465  -> false) in
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
      let uu____5487 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5487 with
      | (u,uu____5505,g_u) ->
          let g =
            let uu____5520 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5520;
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
      let uu____5537 = goal_of_goal_ty env typ in
      match uu____5537 with
      | (g,g_u) ->
          let ps =
            {
              FStar_Tactics_Types.main_context = env;
              FStar_Tactics_Types.main_goal = g;
              FStar_Tactics_Types.all_implicits =
                (g_u.FStar_TypeChecker_Env.implicits);
              FStar_Tactics_Types.goals = [g];
              FStar_Tactics_Types.smt_goals = []
            } in
          (ps, (g.FStar_Tactics_Types.witness))