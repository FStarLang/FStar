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
        let uu____312 = FStar_Util.string_of_int ps.FStar_Tactics_Types.depth in
        let uu____313 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.goals) in
        let uu____314 =
          let uu____315 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.goals in
          FStar_String.concat "\n" uu____315 in
        let uu____318 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.smt_goals) in
        let uu____319 =
          let uu____320 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.smt_goals in
          FStar_String.concat "\n" uu____320 in
        FStar_Util.format6
          "State dump @ depth %s(%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s"
          uu____312 msg uu____313 uu____314 uu____318 uu____319
let goal_to_json: FStar_Tactics_Types.goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____328 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____328 FStar_Syntax_Print.binders_to_json in
    let uu____329 =
      let uu____336 =
        let uu____343 =
          let uu____348 =
            let uu____349 =
              let uu____356 =
                let uu____361 =
                  let uu____362 =
                    FStar_TypeChecker_Normalize.term_to_string
                      g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness in
                  FStar_Util.JsonStr uu____362 in
                ("witness", uu____361) in
              let uu____363 =
                let uu____370 =
                  let uu____375 =
                    let uu____376 =
                      FStar_TypeChecker_Normalize.term_to_string
                        g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty in
                    FStar_Util.JsonStr uu____376 in
                  ("type", uu____375) in
                [uu____370] in
              uu____356 :: uu____363 in
            FStar_Util.JsonAssoc uu____349 in
          ("goal", uu____348) in
        [uu____343] in
      ("hyps", g_binders) :: uu____336 in
    FStar_Util.JsonAssoc uu____329
let ps_to_json:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____408  ->
    match uu____408 with
    | (msg,ps) ->
        let uu____415 =
          let uu____422 =
            let uu____429 =
              let uu____434 =
                let uu____435 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals in
                FStar_Util.JsonList uu____435 in
              ("goals", uu____434) in
            let uu____438 =
              let uu____445 =
                let uu____450 =
                  let uu____451 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals in
                  FStar_Util.JsonList uu____451 in
                ("smt-goals", uu____450) in
              [uu____445] in
            uu____429 :: uu____438 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____422 in
        FStar_Util.JsonAssoc uu____415
let fstar_refl_binder_lid: FStar_Ident.lident =
  FStar_Reflection_Data.fstar_refl_types_lid "binder"
let dump_proofstate:
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Normalize.psc -> Prims.string -> Prims.unit
  =
  fun ps  ->
    fun ctxt  ->
      fun msg  ->
        FStar_Options.with_saved_options
          (fun uu____487  ->
             FStar_Options.set_option "print_effect_args"
               (FStar_Options.Bool true);
             (let subst1 = FStar_TypeChecker_Normalize.psc_subst ctxt in
              (let uu____491 = FStar_Syntax_Print.subst_to_string subst1 in
               FStar_Util.print1 "psc substitution: %s\n" uu____491);
              (let ps1 = FStar_Tactics_Types.subst_proof_state subst1 ps in
               FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
                 (msg, ps1))))
let print_proof_state1: Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac (fun p  -> dump_cur p msg; FStar_Tactics_Result.Success ((), p))
let print_proof_state:
  FStar_TypeChecker_Normalize.psc -> Prims.string -> Prims.unit tac =
  fun ctxt  ->
    fun msg  ->
      mk_tac
        (fun p  ->
           dump_proofstate p ctxt msg; FStar_Tactics_Result.Success ((), p))
let get: FStar_Tactics_Types.proofstate tac =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p))
let tac_verb_dbg: Prims.bool FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let rec log:
  FStar_Tactics_Types.proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit
  =
  fun ps  ->
    fun f  ->
      let uu____555 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____555 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____609 =
              let uu____612 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____612 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____609);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail: 'Auu____684 . Prims.string -> 'Auu____684 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____695 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____695
          then
            dump_proofstate ps FStar_TypeChecker_Normalize.null_psc
              (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____703 . Prims.string -> Prims.string -> 'Auu____703 tac =
  fun msg  ->
    fun x  -> let uu____714 = FStar_Util.format1 msg x in fail uu____714
let fail2:
  'Auu____723 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____723 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____738 = FStar_Util.format2 msg x y in fail uu____738
let fail3:
  'Auu____749 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____749 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____768 = FStar_Util.format3 msg x y z in fail uu____768
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____796 = run t ps in
         match uu____796 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success
                ((FStar_Pervasives_Native.Some a), q))
         | FStar_Tactics_Result.Failed (uu____810,uu____811) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____826  -> FStar_Tactics_Result.Success ((), p))
let do_unify:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        try FStar_TypeChecker_Rel.teq_nosmt env t1 t2
        with | uu____844 -> false
let trysolve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____858 =
         let uu___112_859 = p in
         let uu____860 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___112_859.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___112_859.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___112_859.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____860;
           FStar_Tactics_Types.smt_goals =
             (uu___112_859.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___112_859.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___112_859.FStar_Tactics_Types.__dump)
         } in
       set uu____858)
let solve:
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____875 = trysolve goal solution in
      if uu____875
      then dismiss
      else
        (let uu____879 =
           let uu____880 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context solution in
           let uu____881 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness in
           let uu____882 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           FStar_Util.format3 "%s does not solve %s : %s" uu____880 uu____881
             uu____882 in
         fail uu____879)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___113_889 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___113_889.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___113_889.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___113_889.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___113_889.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___113_889.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___113_889.FStar_Tactics_Types.__dump)
          }))
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___114_906 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___114_906.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___114_906.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___114_906.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___114_906.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___114_906.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___114_906.FStar_Tactics_Types.__dump)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___115_923 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___115_923.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___115_923.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___115_923.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___115_923.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___115_923.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___115_923.FStar_Tactics_Types.__dump)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___116_940 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___116_940.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___116_940.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___116_940.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___116_940.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___116_940.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___116_940.FStar_Tactics_Types.__dump)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___117_957 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___117_957.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___117_957.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___117_957.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___117_957.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___117_957.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___117_957.FStar_Tactics_Types.__dump)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____967  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___118_980 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___118_980.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___118_980.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___118_980.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___118_980.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___118_980.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___118_980.FStar_Tactics_Types.__dump)
            }))
let new_uvar: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun typ  ->
      let uu____1005 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____1005 with
      | (u,uu____1021,g_u) ->
          let uu____1035 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____1035 (fun uu____1039  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1044 = FStar_Syntax_Util.un_squash t in
    match uu____1044 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1054 =
          let uu____1055 = FStar_Syntax_Subst.compress t' in
          uu____1055.FStar_Syntax_Syntax.n in
        (match uu____1054 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1059 -> false)
    | uu____1060 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1069 = FStar_Syntax_Util.un_squash t in
    match uu____1069 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1079 =
          let uu____1080 = FStar_Syntax_Subst.compress t' in
          uu____1080.FStar_Syntax_Syntax.n in
        (match uu____1079 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1084 -> false)
    | uu____1085 -> false
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
        let uu____1119 = new_uvar env typ in
        bind uu____1119
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
        let uu____1142 = mk_irrelevant_goal env phi opts in
        bind uu____1142 (fun goal  -> add_goals [goal])
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
       let uu____1164 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1164
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1168 =
            FStar_TypeChecker_Normalize.term_to_string
              goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1168))
let add_goal_from_guard:
  env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Options.optionstate -> Prims.unit tac
  =
  fun e  ->
    fun g  ->
      fun opts  ->
        let uu____1185 =
          let uu____1186 = FStar_TypeChecker_Rel.simplify_guard e g in
          uu____1186.FStar_TypeChecker_Env.guard_f in
        match uu____1185 with
        | FStar_TypeChecker_Common.Trivial  -> ret ()
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu____1190 = istrivial e f in
            if uu____1190
            then ret ()
            else
              (let uu____1194 = mk_irrelevant_goal e f opts in
               bind uu____1194
                 (fun goal  ->
                    let goal1 =
                      let uu___119_1201 = goal in
                      {
                        FStar_Tactics_Types.context =
                          (uu___119_1201.FStar_Tactics_Types.context);
                        FStar_Tactics_Types.witness =
                          (uu___119_1201.FStar_Tactics_Types.witness);
                        FStar_Tactics_Types.goal_ty =
                          (uu___119_1201.FStar_Tactics_Types.goal_ty);
                        FStar_Tactics_Types.opts =
                          (uu___119_1201.FStar_Tactics_Types.opts);
                        FStar_Tactics_Types.is_guard = true
                      } in
                    push_goals [goal1]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1207 = is_irrelevant g in
       if uu____1207
       then bind dismiss (fun uu____1211  -> add_smt_goals [g])
       else
         (let uu____1213 =
            FStar_TypeChecker_Normalize.term_to_string
              g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1213))
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
             let uu____1259 =
               try
                 let uu____1293 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1293
               with | uu____1323 -> fail "divide: not enough goals" in
             bind uu____1259
               (fun uu____1350  ->
                  match uu____1350 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___120_1376 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___120_1376.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___120_1376.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___120_1376.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___120_1376.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___120_1376.FStar_Tactics_Types.__dump)
                        } in
                      let rp =
                        let uu___121_1378 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___121_1378.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___121_1378.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___121_1378.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___121_1378.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___121_1378.FStar_Tactics_Types.__dump)
                        } in
                      let uu____1379 = set lp in
                      bind uu____1379
                        (fun uu____1387  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1401 = set rp in
                                     bind uu____1401
                                       (fun uu____1409  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___122_1425 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___122_1425.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___122_1425.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___122_1425.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___122_1425.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___122_1425.FStar_Tactics_Types.__dump)
                                                      } in
                                                    let uu____1426 = set p' in
                                                    bind uu____1426
                                                      (fun uu____1434  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1454 = divide (Prims.parse_int "1") f idtac in
    bind uu____1454
      (fun uu____1467  -> match uu____1467 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1502::uu____1503 ->
             let uu____1506 =
               let uu____1515 = map tau in
               divide (Prims.parse_int "1") tau uu____1515 in
             bind uu____1506
               (fun uu____1533  ->
                  match uu____1533 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1572 =
        bind t1
          (fun uu____1577  ->
             let uu____1578 = map t2 in
             bind uu____1578 (fun uu____1586  -> ret ())) in
      focus uu____1572
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1597 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1597 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1612 =
             let uu____1613 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1613 in
           if uu____1612
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1619 = new_uvar env' typ' in
              bind uu____1619
                (fun u  ->
                   let uu____1626 =
                     let uu____1627 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     trysolve goal uu____1627 in
                   if uu____1626
                   then
                     let uu____1630 =
                       let uu____1633 =
                         let uu___125_1634 = goal in
                         let uu____1635 = bnorm env' u in
                         let uu____1636 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1635;
                           FStar_Tactics_Types.goal_ty = uu____1636;
                           FStar_Tactics_Types.opts =
                             (uu___125_1634.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___125_1634.FStar_Tactics_Types.is_guard)
                         } in
                       replace_cur uu____1633 in
                     bind uu____1630 (fun uu____1638  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1644 =
             FStar_TypeChecker_Normalize.term_to_string
               goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1644)
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
       (let uu____1665 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1665 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1684 =
              let uu____1685 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1685 in
            if uu____1684
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1701 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1701; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1703 =
                 let uu____1706 = comp_to_typ c in new_uvar env' uu____1706 in
               bind uu____1703
                 (fun u  ->
                    let lb =
                      let uu____1722 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____1722 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1726 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1726 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        let res = trysolve goal tm in
                        if res
                        then
                          let uu____1763 =
                            let uu____1766 =
                              let uu___126_1767 = goal in
                              let uu____1768 = bnorm env' u in
                              let uu____1769 =
                                let uu____1770 = comp_to_typ c in
                                bnorm env' uu____1770 in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____1768;
                                FStar_Tactics_Types.goal_ty = uu____1769;
                                FStar_Tactics_Types.opts =
                                  (uu___126_1767.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___126_1767.FStar_Tactics_Types.is_guard)
                              } in
                            replace_cur uu____1766 in
                          bind uu____1763
                            (fun uu____1777  ->
                               let uu____1778 =
                                 let uu____1783 =
                                   FStar_Syntax_Syntax.mk_binder bv in
                                 (uu____1783, b) in
                               ret uu____1778)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____1797 =
              FStar_TypeChecker_Normalize.term_to_string
                goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1797))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____1822 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1822 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___127_1829 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___127_1829.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___127_1829.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___127_1829.FStar_Tactics_Types.is_guard)
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
             let uu____1853 = FStar_TypeChecker_Normalize.tr_norm_steps s in
             FStar_List.append
               [FStar_TypeChecker_Normalize.Reify;
               FStar_TypeChecker_Normalize.UnfoldTac] uu____1853 in
           let t1 = normalize steps ps.FStar_Tactics_Types.main_context t in
           ret t1)
let __exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1868 =
           try
             let uu____1896 =
               (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
                 goal.FStar_Tactics_Types.context t in
             ret uu____1896
           with
           | e ->
               let uu____1923 = FStar_Syntax_Print.term_to_string t in
               let uu____1924 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1923
                 uu____1924 in
         bind uu____1868
           (fun uu____1942  ->
              match uu____1942 with
              | (t1,typ,guard) ->
                  let uu____1954 =
                    let uu____1955 =
                      let uu____1956 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1956 in
                    Prims.op_Negation uu____1955 in
                  if uu____1954
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1960 =
                       do_unify goal.FStar_Tactics_Types.context typ
                         goal.FStar_Tactics_Types.goal_ty in
                     if uu____1960
                     then solve goal t1
                     else
                       (let uu____1964 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context t1 in
                        let uu____1965 =
                          let uu____1966 =
                            bnorm goal.FStar_Tactics_Types.context typ in
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context uu____1966 in
                        let uu____1967 =
                          FStar_TypeChecker_Normalize.term_to_string
                            goal.FStar_Tactics_Types.context
                            goal.FStar_Tactics_Types.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1964 uu____1965 uu____1967))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  -> let uu____1976 = __exact t in focus uu____1976
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1990 =
           try
             let uu____2018 =
               FStar_TypeChecker_TcTerm.tc_term
                 goal.FStar_Tactics_Types.context t in
             ret uu____2018
           with
           | e ->
               let uu____2045 = FStar_Syntax_Print.term_to_string t in
               let uu____2046 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2045
                 uu____2046 in
         bind uu____1990
           (fun uu____2064  ->
              match uu____2064 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2082 =
                       let uu____2083 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____2083 in
                     if uu____2082
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2087 =
                          let uu____2096 =
                            let uu____2105 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____2105.FStar_Syntax_Syntax.effect_args in
                          match uu____2096 with
                          | pre::post::uu____2116 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2157 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____2087 with
                        | (pre,post) ->
                            let uu____2186 =
                              do_unify goal.FStar_Tactics_Types.context post
                                goal.FStar_Tactics_Types.goal_ty in
                            if uu____2186
                            then
                              let uu____2189 = solve goal t1 in
                              bind uu____2189
                                (fun uu____2193  ->
                                   add_irrelevant_goal
                                     goal.FStar_Tactics_Types.context pre
                                     goal.FStar_Tactics_Types.opts)
                            else
                              (let uu____2195 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context t1 in
                               let uu____2196 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context post in
                               let uu____2197 =
                                 FStar_TypeChecker_Normalize.term_to_string
                                   goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2195 uu____2196 uu____2197)))))
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2210 =
             let uu____2217 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
             FStar_Util.set_elements uu____2217 in
           FStar_List.map FStar_Pervasives_Native.fst uu____2210 in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2244 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2264 =
               let uu____2269 = __exact tm in trytac uu____2269 in
             bind uu____2264
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2282 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2282 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           let uu____2312 =
                             let uu____2313 =
                               FStar_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu____2313 in
                           if uu____2312
                           then fail "apply: not total codomain"
                           else
                             (let uu____2317 =
                                new_uvar goal.FStar_Tactics_Types.context
                                  bv.FStar_Syntax_Syntax.sort in
                              bind uu____2317
                                (fun u  ->
                                   let tm' =
                                     FStar_Syntax_Syntax.mk_Tm_app tm
                                       [(u, aq)] FStar_Pervasives_Native.None
                                       (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                   let typ' =
                                     let uu____2337 = comp_to_typ c in
                                     FStar_All.pipe_left
                                       (FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.NT (bv, u)])
                                       uu____2337 in
                                   let uu____2338 = __apply uopt tm' typ' in
                                   bind uu____2338
                                     (fun uu____2346  ->
                                        let u1 =
                                          bnorm
                                            goal.FStar_Tactics_Types.context
                                            u in
                                        let uu____2348 =
                                          let uu____2349 =
                                            let uu____2352 =
                                              let uu____2353 =
                                                FStar_Syntax_Util.head_and_args
                                                  u1 in
                                              FStar_Pervasives_Native.fst
                                                uu____2353 in
                                            FStar_Syntax_Subst.compress
                                              uu____2352 in
                                          uu____2349.FStar_Syntax_Syntax.n in
                                        match uu____2348 with
                                        | FStar_Syntax_Syntax.Tm_uvar
                                            (uvar,uu____2381) ->
                                            bind get
                                              (fun ps  ->
                                                 let uu____2409 =
                                                   uopt &&
                                                     (uvar_free uvar ps) in
                                                 if uu____2409
                                                 then ret ()
                                                 else
                                                   (let uu____2413 =
                                                      let uu____2416 =
                                                        let uu___132_2417 =
                                                          goal in
                                                        let uu____2418 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            u1 in
                                                        let uu____2419 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          FStar_Tactics_Types.context
                                                            =
                                                            (uu___132_2417.FStar_Tactics_Types.context);
                                                          FStar_Tactics_Types.witness
                                                            = uu____2418;
                                                          FStar_Tactics_Types.goal_ty
                                                            = uu____2419;
                                                          FStar_Tactics_Types.opts
                                                            =
                                                            (uu___132_2417.FStar_Tactics_Types.opts);
                                                          FStar_Tactics_Types.is_guard
                                                            = false
                                                        } in
                                                      [uu____2416] in
                                                    add_goals uu____2413))
                                        | t -> ret ()))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2478 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2478 with
           | (tm1,typ,guard) ->
               let uu____2490 =
                 let uu____2493 =
                   let uu____2496 = __apply uopt tm1 typ in
                   bind uu____2496
                     (fun uu____2500  ->
                        add_goal_from_guard goal.FStar_Tactics_Types.context
                          guard goal.FStar_Tactics_Types.opts) in
                 focus uu____2493 in
               let uu____2501 =
                 let uu____2504 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context tm1 in
                 let uu____2505 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context typ in
                 let uu____2506 =
                   FStar_TypeChecker_Normalize.term_to_string
                     goal.FStar_Tactics_Types.context
                     goal.FStar_Tactics_Types.goal_ty in
                 fail3
                   "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                   uu____2504 uu____2505 uu____2506 in
               try_unif uu____2490 uu____2501)
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____2515 =
      let is_unit_t t =
        let uu____2522 =
          let uu____2523 = FStar_Syntax_Subst.compress t in
          uu____2523.FStar_Syntax_Syntax.n in
        match uu____2522 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
            true
        | uu____2527 -> false in
      bind cur_goal
        (fun goal  ->
           let uu____2537 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2537 with
           | (tm1,t,guard) ->
               let uu____2549 = FStar_Syntax_Util.arrow_formals_comp t in
               (match uu____2549 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2579 =
                         FStar_List.fold_left
                           (fun uu____2625  ->
                              fun uu____2626  ->
                                match (uu____2625, uu____2626) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2729 = is_unit_t b_t in
                                    if uu____2729
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____2767 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.FStar_Tactics_Types.context
                                           b_t in
                                       match uu____2767 with
                                       | (u,uu____2797,g_u) ->
                                           let uu____2811 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____2811,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2579 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____2881 =
                             let uu____2890 =
                               let uu____2899 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____2899.FStar_Syntax_Syntax.effect_args in
                             match uu____2890 with
                             | pre::post::uu____2910 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____2951 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____2881 with
                            | (pre,post) ->
                                let uu____2980 =
                                  let uu____2981 =
                                    let uu____2982 =
                                      FStar_Syntax_Util.mk_squash post in
                                    do_unify goal.FStar_Tactics_Types.context
                                      uu____2982
                                      goal.FStar_Tactics_Types.goal_ty in
                                  Prims.op_Negation uu____2981 in
                                if uu____2980
                                then
                                  let uu____2985 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context tm1 in
                                  let uu____2986 =
                                    let uu____2987 =
                                      FStar_Syntax_Util.mk_squash post in
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context
                                      uu____2987 in
                                  let uu____2988 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      goal.FStar_Tactics_Types.context
                                      goal.FStar_Tactics_Types.goal_ty in
                                  fail3
                                    "apply_lemma: Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                    uu____2985 uu____2986 uu____2988
                                else
                                  (let solution =
                                     let uu____2991 =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       goal.FStar_Tactics_Types.context
                                       uu____2991 in
                                   let implicits1 =
                                     FStar_All.pipe_right
                                       implicits.FStar_TypeChecker_Env.implicits
                                       (FStar_List.filter
                                          (fun uu____3059  ->
                                             match uu____3059 with
                                             | (uu____3072,uu____3073,uu____3074,tm2,uu____3076,uu____3077)
                                                 ->
                                                 let uu____3078 =
                                                   FStar_Syntax_Util.head_and_args
                                                     tm2 in
                                                 (match uu____3078 with
                                                  | (hd1,uu____3094) ->
                                                      let uu____3115 =
                                                        let uu____3116 =
                                                          FStar_Syntax_Subst.compress
                                                            hd1 in
                                                        uu____3116.FStar_Syntax_Syntax.n in
                                                      (match uu____3115 with
                                                       | FStar_Syntax_Syntax.Tm_uvar
                                                           uu____3119 -> true
                                                       | uu____3136 -> false)))) in
                                   let uu____3137 = solve goal solution in
                                   bind uu____3137
                                     (fun uu____3142  ->
                                        let uu____3143 =
                                          add_implicits implicits1 in
                                        bind uu____3143
                                          (fun uu____3154  ->
                                             let is_free_uvar uv t1 =
                                               let free_uvars =
                                                 let uu____3165 =
                                                   let uu____3172 =
                                                     FStar_Syntax_Free.uvars
                                                       t1 in
                                                   FStar_Util.set_elements
                                                     uu____3172 in
                                                 FStar_List.map
                                                   FStar_Pervasives_Native.fst
                                                   uu____3165 in
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
                                               let uu____3213 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t1 in
                                               match uu____3213 with
                                               | (hd1,uu____3229) ->
                                                   (match hd1.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_uvar
                                                        (uv,uu____3251) ->
                                                        appears uv goals
                                                    | uu____3276 -> false) in
                                             let sub_goals =
                                               FStar_All.pipe_right
                                                 implicits1
                                                 (FStar_List.map
                                                    (fun uu____3318  ->
                                                       match uu____3318 with
                                                       | (_msg,_env,_uvar,term,typ,uu____3336)
                                                           ->
                                                           let uu___135_3337
                                                             = goal in
                                                           let uu____3338 =
                                                             bnorm
                                                               goal.FStar_Tactics_Types.context
                                                               term in
                                                           let uu____3339 =
                                                             bnorm
                                                               goal.FStar_Tactics_Types.context
                                                               typ in
                                                           {
                                                             FStar_Tactics_Types.context
                                                               =
                                                               (uu___135_3337.FStar_Tactics_Types.context);
                                                             FStar_Tactics_Types.witness
                                                               = uu____3338;
                                                             FStar_Tactics_Types.goal_ty
                                                               = uu____3339;
                                                             FStar_Tactics_Types.opts
                                                               =
                                                               (uu___135_3337.FStar_Tactics_Types.opts);
                                                             FStar_Tactics_Types.is_guard
                                                               =
                                                               (uu___135_3337.FStar_Tactics_Types.is_guard)
                                                           })) in
                                             let rec filter' f xs =
                                               match xs with
                                               | [] -> []
                                               | x::xs1 ->
                                                   let uu____3377 = f x xs1 in
                                                   if uu____3377
                                                   then
                                                     let uu____3380 =
                                                       filter' f xs1 in
                                                     x :: uu____3380
                                                   else filter' f xs1 in
                                             let sub_goals1 =
                                               filter'
                                                 (fun g  ->
                                                    fun goals  ->
                                                      let uu____3394 =
                                                        checkone
                                                          g.FStar_Tactics_Types.witness
                                                          goals in
                                                      Prims.op_Negation
                                                        uu____3394) sub_goals in
                                             let uu____3395 =
                                               add_goal_from_guard
                                                 goal.FStar_Tactics_Types.context
                                                 guard
                                                 goal.FStar_Tactics_Types.opts in
                                             bind uu____3395
                                               (fun uu____3400  ->
                                                  let uu____3401 =
                                                    let uu____3404 =
                                                      let uu____3405 =
                                                        let uu____3406 =
                                                          FStar_Syntax_Util.mk_squash
                                                            pre in
                                                        istrivial
                                                          goal.FStar_Tactics_Types.context
                                                          uu____3406 in
                                                      Prims.op_Negation
                                                        uu____3405 in
                                                    if uu____3404
                                                    then
                                                      add_irrelevant_goal
                                                        goal.FStar_Tactics_Types.context
                                                        pre
                                                        goal.FStar_Tactics_Types.opts
                                                    else ret () in
                                                  bind uu____3401
                                                    (fun uu____3411  ->
                                                       add_goals sub_goals1))))))))) in
    focus uu____2515
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3428 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3428 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3438::(e1,uu____3440)::(e2,uu____3442)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3501 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3524 = destruct_eq' typ in
    match uu____3524 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3554 = FStar_Syntax_Util.un_squash typ in
        (match uu____3554 with
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
        let uu____3612 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____3612 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____3660 = aux e' in
               FStar_Util.map_opt uu____3660
                 (fun uu____3684  ->
                    match uu____3684 with | (e'',bvs) -> (e'', (bv' :: bvs)))) in
      let uu____3705 = aux e in
      FStar_Util.map_opt uu____3705
        (fun uu____3729  ->
           match uu____3729 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
let push_bvs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env
  =
  fun e  ->
    fun bvs  ->
      FStar_List.fold_right
        (fun b  -> fun e1  -> FStar_TypeChecker_Env.push_bv e1 b) bvs e
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
          let uu____3790 = split_env b1 g.FStar_Tactics_Types.context in
          FStar_Util.map_opt uu____3790
            (fun uu____3814  ->
               match uu____3814 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___136_3831 = bv in
                     let uu____3832 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___136_3831.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___136_3831.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____3832
                     } in
                   let bvs1 = FStar_List.map s1 bvs in
                   let c = push_bvs e0 (b2 :: bvs1) in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty in
                   let uu___137_3841 = g in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___137_3841.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___137_3841.FStar_Tactics_Types.is_guard)
                   })
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3856 = h in
         match uu____3856 with
         | (bv,uu____3860) ->
             let uu____3861 =
               FStar_All.pipe_left mlog
                 (fun uu____3871  ->
                    let uu____3872 = FStar_Syntax_Print.bv_to_string bv in
                    let uu____3873 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3872
                      uu____3873) in
             bind uu____3861
               (fun uu____3876  ->
                  let uu____3877 =
                    split_env bv goal.FStar_Tactics_Types.context in
                  match uu____3877 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____3906 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort in
                      (match uu____3906 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____3921 =
                             let uu____3922 = FStar_Syntax_Subst.compress x in
                             uu____3922.FStar_Syntax_Syntax.n in
                           (match uu____3921 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                let s1 bv1 =
                                  let uu___138_3935 = bv1 in
                                  let uu____3936 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___138_3935.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___138_3935.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____3936
                                  } in
                                let bvs1 = FStar_List.map s1 bvs in
                                let uu____3942 =
                                  let uu___139_3943 = goal in
                                  let uu____3944 = push_bvs e0 (bv :: bvs1) in
                                  let uu____3945 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness in
                                  let uu____3946 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty in
                                  {
                                    FStar_Tactics_Types.context = uu____3944;
                                    FStar_Tactics_Types.witness = uu____3945;
                                    FStar_Tactics_Types.goal_ty = uu____3946;
                                    FStar_Tactics_Types.opts =
                                      (uu___139_3943.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___139_3943.FStar_Tactics_Types.is_guard)
                                  } in
                                replace_cur uu____3942
                            | uu____3947 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____3948 ->
                           fail "rewrite: Not an equality hypothesis")))
let rename_to: FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____3975 = b in
           match uu____3975 with
           | (bv,uu____3979) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___140_3983 = bv in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___140_3983.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___140_3983.FStar_Syntax_Syntax.sort)
                    }) in
               let s1 =
                 let uu____3987 =
                   let uu____3988 =
                     let uu____3995 = FStar_Syntax_Syntax.bv_to_name bv' in
                     (bv, uu____3995) in
                   FStar_Syntax_Syntax.NT uu____3988 in
                 [uu____3987] in
               let uu____3996 = subst_goal bv bv' s1 goal in
               (match uu____3996 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
let binder_retype: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4016 = b in
         match uu____4016 with
         | (bv,uu____4020) ->
             let uu____4021 = split_env bv goal.FStar_Tactics_Types.context in
             (match uu____4021 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4050 = FStar_Syntax_Util.type_u () in
                  (match uu____4050 with
                   | (ty,u) ->
                       let uu____4059 = new_uvar e0 ty in
                       bind uu____4059
                         (fun t'  ->
                            let bv'' =
                              let uu___141_4069 = bv in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___141_4069.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___141_4069.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              } in
                            let s =
                              let uu____4073 =
                                let uu____4074 =
                                  let uu____4081 =
                                    FStar_Syntax_Syntax.bv_to_name bv'' in
                                  (bv, uu____4081) in
                                FStar_Syntax_Syntax.NT uu____4074 in
                              [uu____4073] in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___142_4089 = b1 in
                                   let uu____4090 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___142_4089.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___142_4089.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4090
                                   }) bvs in
                            let env' = push_bvs e0 (bv'' :: bvs1) in
                            bind dismiss
                              (fun uu____4096  ->
                                 let uu____4097 =
                                   let uu____4100 =
                                     let uu____4103 =
                                       let uu___143_4104 = goal in
                                       let uu____4105 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness in
                                       let uu____4106 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4105;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4106;
                                         FStar_Tactics_Types.opts =
                                           (uu___143_4104.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___143_4104.FStar_Tactics_Types.is_guard)
                                       } in
                                     [uu____4103] in
                                   add_goals uu____4100 in
                                 bind uu____4097
                                   (fun uu____4109  ->
                                      let uu____4110 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t' in
                                      add_irrelevant_goal e0 uu____4110
                                        goal.FStar_Tactics_Types.opts))))))
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4116 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4116 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4138 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4138 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___144_4172 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___144_4172.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___144_4172.FStar_Tactics_Types.is_guard)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4184 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4184 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4205 = FStar_Syntax_Print.bv_to_string x in
               let uu____4206 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4205 uu____4206
             else revert)
let clear_top: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4213 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____4213 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____4235 = FStar_Util.set_mem x fns_ty in
           if uu____4235
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4239 = new_uvar env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____4239
                (fun u  ->
                   let uu____4245 =
                     let uu____4246 = trysolve goal u in
                     Prims.op_Negation uu____4246 in
                   if uu____4245
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___145_4251 = goal in
                        let uu____4252 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____4252;
                          FStar_Tactics_Types.goal_ty =
                            (uu___145_4251.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___145_4251.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___145_4251.FStar_Tactics_Types.is_guard)
                        } in
                      bind dismiss (fun uu____4254  -> add_goals [new_goal])))))
let rec clear: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4266 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____4266 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____4290  ->
                    let uu____4291 = clear b in
                    bind uu____4291
                      (fun uu____4295  ->
                         bind intro (fun uu____4297  -> ret ()))))
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___146_4314 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___146_4314.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___146_4314.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___146_4314.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___146_4314.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4316  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___147_4333 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___147_4333.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___147_4333.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___147_4333.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___147_4333.FStar_Tactics_Types.is_guard)
           } in
         bind dismiss (fun uu____4335  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4377 = f x in
          bind uu____4377
            (fun y  ->
               let uu____4385 = mapM f xs in
               bind uu____4385 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____4431 = FStar_Syntax_Subst.compress t in
          uu____4431.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____4466 = ff hd1 in
              bind uu____4466
                (fun hd2  ->
                   let fa uu____4486 =
                     match uu____4486 with
                     | (a,q) ->
                         let uu____4499 = ff a in
                         bind uu____4499 (fun a1  -> ret (a1, q)) in
                   let uu____4512 = mapM fa args in
                   bind uu____4512
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4572 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____4572 with
               | (bs1,t') ->
                   let uu____4581 =
                     let uu____4584 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____4584 t' in
                   bind uu____4581
                     (fun t''  ->
                        let uu____4588 =
                          let uu____4589 =
                            let uu____4606 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____4607 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____4606, uu____4607, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____4589 in
                        ret uu____4588))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4628 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___148_4632 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___148_4632.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___148_4632.FStar_Syntax_Syntax.vars)
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
            let uu____4661 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4661 with
            | (t1,lcomp,g) ->
                let uu____4673 =
                  (let uu____4676 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp in
                   Prims.op_Negation uu____4676) ||
                    (let uu____4678 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4678) in
                if uu____4673
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4685 = new_uvar env typ in
                   bind uu____4685
                     (fun ut  ->
                        log ps
                          (fun uu____4696  ->
                             let uu____4697 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4698 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4697 uu____4698);
                        (let uu____4699 =
                           let uu____4702 =
                             let uu____4703 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4703 typ t1 ut in
                           add_irrelevant_goal env uu____4702 opts in
                         bind uu____4699
                           (fun uu____4706  ->
                              let uu____4707 =
                                bind tau
                                  (fun uu____4712  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4707))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4733 =
           match ps.FStar_Tactics_Types.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4733 with
         | (g,gs) ->
             let gt1 = g.FStar_Tactics_Types.goal_ty in
             (log ps
                (fun uu____4770  ->
                   let uu____4771 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4771);
              bind dismiss_all
                (fun uu____4774  ->
                   let uu____4775 =
                     tac_bottom_fold_env
                       (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                       g.FStar_Tactics_Types.context gt1 in
                   bind uu____4775
                     (fun gt'  ->
                        log ps
                          (fun uu____4785  ->
                             let uu____4786 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4786);
                        (let uu____4787 = push_goals gs in
                         bind uu____4787
                           (fun uu____4791  ->
                              add_goals
                                [(let uu___149_4793 = g in
                                  {
                                    FStar_Tactics_Types.context =
                                      (uu___149_4793.FStar_Tactics_Types.context);
                                    FStar_Tactics_Types.witness =
                                      (uu___149_4793.FStar_Tactics_Types.witness);
                                    FStar_Tactics_Types.goal_ty = gt';
                                    FStar_Tactics_Types.opts =
                                      (uu___149_4793.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___149_4793.FStar_Tactics_Types.is_guard)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4813 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____4813 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4825 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4825 with
            | (hd1,args) ->
                let uu____4858 =
                  let uu____4871 =
                    let uu____4872 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4872.FStar_Syntax_Syntax.n in
                  (uu____4871, args) in
                (match uu____4858 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4886::(l,uu____4888)::(r,uu____4890)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4937 =
                       let uu____4938 =
                         do_unify g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____4938 in
                     if uu____4937
                     then
                       let uu____4941 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context l in
                       let uu____4942 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4941 uu____4942
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____4945) ->
                     let uu____4962 =
                       FStar_TypeChecker_Normalize.term_to_string
                         g.FStar_Tactics_Types.context t in
                     fail1 "trefl: not an equality (%s)" uu____4962))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4970 =
         new_uvar g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
       bind uu____4970
         (fun u  ->
            let g' =
              let uu___150_4977 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___150_4977.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___150_4977.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___150_4977.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___150_4977.FStar_Tactics_Types.is_guard)
              } in
            bind dismiss
              (fun uu____4980  ->
                 let uu____4981 =
                   let uu____4984 =
                     let uu____4985 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4985
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal g.FStar_Tactics_Types.context
                     uu____4984 g.FStar_Tactics_Types.opts in
                 bind uu____4981
                   (fun uu____4988  ->
                      let uu____4989 = add_goals [g'] in
                      bind uu____4989 (fun uu____4993  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___151_5010 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___151_5010.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___151_5010.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___151_5010.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___151_5010.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___151_5010.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___151_5010.FStar_Tactics_Types.__dump)
              })
       | uu____5011 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___152_5026 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___152_5026.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___152_5026.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___152_5026.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___152_5026.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___152_5026.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___152_5026.FStar_Tactics_Types.__dump)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5033 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____5075 =
           (g.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
             g.FStar_Tactics_Types.context t in
         match uu____5075 with
         | (t1,typ,guard) ->
             let uu____5091 = FStar_Syntax_Util.head_and_args typ in
             (match uu____5091 with
              | (hd1,args) ->
                  let uu____5134 =
                    let uu____5147 =
                      let uu____5148 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____5148.FStar_Syntax_Syntax.n in
                    (uu____5147, args) in
                  (match uu____5134 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____5167)::(q,uu____5169)::[]) when
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
                         let uu___153_5207 = g in
                         let uu____5208 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_p in
                         {
                           FStar_Tactics_Types.context = uu____5208;
                           FStar_Tactics_Types.witness =
                             (uu___153_5207.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___153_5207.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___153_5207.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___153_5207.FStar_Tactics_Types.is_guard)
                         } in
                       let g2 =
                         let uu___154_5210 = g in
                         let uu____5211 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_q in
                         {
                           FStar_Tactics_Types.context = uu____5211;
                           FStar_Tactics_Types.witness =
                             (uu___154_5210.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___154_5210.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___154_5210.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___154_5210.FStar_Tactics_Types.is_guard)
                         } in
                       bind dismiss
                         (fun uu____5218  ->
                            let uu____5219 = add_goals [g1; g2] in
                            bind uu____5219
                              (fun uu____5228  ->
                                 let uu____5229 =
                                   let uu____5234 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____5235 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____5234, uu____5235) in
                                 ret uu____5229))
                   | uu____5240 ->
                       let uu____5253 =
                         FStar_TypeChecker_Normalize.term_to_string
                           g.FStar_Tactics_Types.context typ in
                       fail1 "Not a disjunction: %s" uu____5253)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5276 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____5276);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___155_5283 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___155_5283.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___155_5283.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___155_5283.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___155_5283.FStar_Tactics_Types.is_guard)
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
           let uu____5324 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               env tm in
           match uu____5324 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____5353 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____5359 =
              let uu____5360 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5360 in
            new_uvar env uu____5359 in
      bind uu____5353
        (fun typ  ->
           let uu____5372 = new_uvar env typ in
           bind uu____5372 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____5392 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____5392)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____5412  ->
             let uu____5413 = FStar_Options.unsafe_tactic_exec () in
             if uu____5413
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____5419  -> fun uu____5420  -> false) in
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
      let uu____5442 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____5442 with
      | (u,uu____5460,g_u) ->
          let g =
            let uu____5475 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____5475;
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
      let uu____5492 = goal_of_goal_ty env typ in
      match uu____5492 with
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
                (fun ps  ->
                   fun msg  ->
                     dump_proofstate ps FStar_TypeChecker_Normalize.null_psc
                       msg)
            } in
          (ps, (g.FStar_Tactics_Types.witness))