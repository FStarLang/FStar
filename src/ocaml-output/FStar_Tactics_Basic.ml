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
    let uu____192 =
      FStar_Syntax_Print.term_to_string g.FStar_Tactics_Types.witness in
    let uu____193 =
      FStar_Syntax_Print.term_to_string g.FStar_Tactics_Types.goal_ty in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____192 uu____193
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____206 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____206
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____219 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____219
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____236 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____236
let comp_to_typ: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____242) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____252) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: FStar_Tactics_Types.goal -> Prims.bool =
  fun g  ->
    let uu____266 =
      let uu____271 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty in
      FStar_Syntax_Util.un_squash uu____271 in
    match uu____266 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____277 -> false
let dump_goal:
  'Auu____288 . 'Auu____288 -> FStar_Tactics_Types.goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____298 = goal_to_string goal in tacprint uu____298
let dump_cur: FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____308 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____312 = FStar_List.hd ps.FStar_Tactics_Types.goals in
            dump_goal ps uu____312))
let ps_to_string:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu____320  ->
    match uu____320 with
    | (msg,ps) ->
        let uu____327 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.goals) in
        let uu____328 =
          let uu____329 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.goals in
          FStar_String.concat "\n" uu____329 in
        let uu____332 =
          FStar_Util.string_of_int
            (FStar_List.length ps.FStar_Tactics_Types.smt_goals) in
        let uu____333 =
          let uu____334 =
            FStar_List.map goal_to_string ps.FStar_Tactics_Types.smt_goals in
          FStar_String.concat "\n" uu____334 in
        FStar_Util.format5
          "State dump (%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s" msg
          uu____327 uu____328 uu____332 uu____333
let goal_to_json: FStar_Tactics_Types.goal -> FStar_Util.json =
  fun g  ->
    let g_binders =
      let uu____342 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context in
      FStar_All.pipe_right uu____342 FStar_Syntax_Print.binders_to_json in
    let uu____343 =
      let uu____350 =
        let uu____357 =
          let uu____362 =
            let uu____363 =
              let uu____370 =
                let uu____375 =
                  let uu____376 =
                    FStar_Syntax_Print.term_to_string
                      g.FStar_Tactics_Types.witness in
                  FStar_Util.JsonStr uu____376 in
                ("witness", uu____375) in
              let uu____377 =
                let uu____384 =
                  let uu____389 =
                    let uu____390 =
                      FStar_Syntax_Print.term_to_string
                        g.FStar_Tactics_Types.goal_ty in
                    FStar_Util.JsonStr uu____390 in
                  ("type", uu____389) in
                [uu____384] in
              uu____370 :: uu____377 in
            FStar_Util.JsonAssoc uu____363 in
          ("goal", uu____362) in
        [uu____357] in
      ("hyps", g_binders) :: uu____350 in
    FStar_Util.JsonAssoc uu____343
let ps_to_json:
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
  =
  fun uu____422  ->
    match uu____422 with
    | (msg,ps) ->
        let uu____429 =
          let uu____436 =
            let uu____443 =
              let uu____448 =
                let uu____449 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals in
                FStar_Util.JsonList uu____449 in
              ("goals", uu____448) in
            let uu____452 =
              let uu____459 =
                let uu____464 =
                  let uu____465 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals in
                  FStar_Util.JsonList uu____465 in
                ("smt-goals", uu____464) in
              [uu____459] in
            uu____443 :: uu____452 in
          ("label", (FStar_Util.JsonStr msg)) :: uu____436 in
        FStar_Util.JsonAssoc uu____429
let dump_proofstate:
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____494  ->
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
      let uu____554 = FStar_ST.op_Bang tac_verb_dbg in
      match uu____554 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____576 =
              let uu____579 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____579 in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____576);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail: 'Auu____619 . Prims.string -> 'Auu____619 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____630 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____630
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
let fail1: 'Auu____638 . Prims.string -> Prims.string -> 'Auu____638 tac =
  fun msg  ->
    fun x  -> let uu____649 = FStar_Util.format1 msg x in fail uu____649
let fail2:
  'Auu____658 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____658 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____673 = FStar_Util.format2 msg x y in fail uu____673
let fail3:
  'Auu____684 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____684 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____703 = FStar_Util.format3 msg x y z in fail uu____703
let trytac: 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____731 = run t ps in
         match uu____731 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success
                ((FStar_Pervasives_Native.Some a), q))
         | FStar_Tactics_Result.Failed (uu____745,uu____746) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let set: FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____761  -> FStar_Tactics_Result.Success ((), p))
let solve: FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun goal  ->
    fun solution  ->
      let uu____770 =
        FStar_TypeChecker_Rel.teq_nosmt goal.FStar_Tactics_Types.context
          goal.FStar_Tactics_Types.witness solution in
      if uu____770
      then ()
      else
        (let uu____772 =
           let uu____773 =
             let uu____774 = FStar_Syntax_Print.term_to_string solution in
             let uu____775 =
               FStar_Syntax_Print.term_to_string
                 goal.FStar_Tactics_Types.witness in
             let uu____776 =
               FStar_Syntax_Print.term_to_string
                 goal.FStar_Tactics_Types.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____774
               uu____775 uu____776 in
           TacFailure uu____773 in
         FStar_Exn.raise uu____772)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____782 =
         let uu___86_783 = p in
         let uu____784 = FStar_List.tl p.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___86_783.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___86_783.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___86_783.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____784;
           FStar_Tactics_Types.smt_goals =
             (uu___86_783.FStar_Tactics_Types.smt_goals)
         } in
       set uu____782)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___87_793 = p in
          {
            FStar_Tactics_Types.main_context =
              (uu___87_793.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___87_793.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___87_793.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___87_793.FStar_Tactics_Types.smt_goals)
          }))
let add_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___88_810 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___88_810.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___88_810.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___88_810.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___88_810.FStar_Tactics_Types.smt_goals)
            }))
let add_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___89_827 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___89_827.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___89_827.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___89_827.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___89_827.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals)
            }))
let push_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___90_844 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___90_844.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___90_844.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___90_844.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___90_844.FStar_Tactics_Types.smt_goals)
            }))
let push_smt_goals: FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___91_861 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___91_861.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___91_861.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___91_861.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___91_861.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs)
            }))
let replace_cur: FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____871  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___92_884 = p in
            {
              FStar_Tactics_Types.main_context =
                (uu___92_884.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___92_884.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___92_884.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___92_884.FStar_Tactics_Types.smt_goals)
            }))
let new_uvar: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun typ  ->
      let uu____909 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____909 with
      | (u,uu____925,g_u) ->
          let uu____939 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____939 (fun uu____943  -> ret u)
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____948 = FStar_Syntax_Util.un_squash t in
    match uu____948 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____958 =
          let uu____959 = FStar_Syntax_Subst.compress t' in
          uu____959.FStar_Syntax_Syntax.n in
        (match uu____958 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____963 -> false)
    | uu____964 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____973 = FStar_Syntax_Util.un_squash t in
    match uu____973 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____983 =
          let uu____984 = FStar_Syntax_Subst.compress t' in
          uu____984.FStar_Syntax_Syntax.n in
        (match uu____983 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____988 -> false)
    | uu____989 -> false
let cur_goal: FStar_Tactics_Types.goal tac =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let add_irrelevant_goal:
  env ->
    FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun env  ->
    fun phi  ->
      fun opts  ->
        let typ = FStar_Syntax_Util.mk_squash phi in
        let uu____1023 = new_uvar env typ in
        bind uu____1023
          (fun u  ->
             let goal =
               {
                 FStar_Tactics_Types.context = env;
                 FStar_Tactics_Types.witness = u;
                 FStar_Tactics_Types.goal_ty = typ;
                 FStar_Tactics_Types.opts = opts
               } in
             add_goals [goal])
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1035 = is_irrelevant g in
       if uu____1035
       then bind dismiss (fun uu____1039  -> add_smt_goals [g])
       else
         (let uu____1041 =
            FStar_Syntax_Print.term_to_string g.FStar_Tactics_Types.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1041))
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
             let uu____1087 =
               try
                 let uu____1121 =
                   FStar_List.splitAt n1 p.FStar_Tactics_Types.goals in
                 ret uu____1121
               with | uu____1151 -> fail "divide: not enough goals" in
             bind uu____1087
               (fun uu____1178  ->
                  match uu____1178 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___93_1204 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___93_1204.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___93_1204.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___93_1204.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = []
                        } in
                      let rp =
                        let uu___94_1206 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___94_1206.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___94_1206.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___94_1206.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = []
                        } in
                      let uu____1207 = set lp in
                      bind uu____1207
                        (fun uu____1215  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1229 = set rp in
                                     bind uu____1229
                                       (fun uu____1237  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___95_1253 = p in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___95_1253.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___95_1253.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___95_1253.FStar_Tactics_Types.all_implicits);
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
                                                    let uu____1254 = set p' in
                                                    bind uu____1254
                                                      (fun uu____1262  ->
                                                         ret (a, b))))))))))
let focus: 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1282 = divide (Prims.parse_int "1") f idtac in
    bind uu____1282
      (fun uu____1295  -> match uu____1295 with | (a,()) -> ret a)
let rec map: 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1330::uu____1331 ->
             let uu____1334 =
               let uu____1343 = map tau in
               divide (Prims.parse_int "1") tau uu____1343 in
             bind uu____1334
               (fun uu____1361  ->
                  match uu____1361 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1400 =
        bind t1
          (fun uu____1405  ->
             let uu____1406 = map t2 in
             bind uu____1406 (fun uu____1414  -> ret ())) in
      focus uu____1400
let intro: FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____1425 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
       match uu____1425 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1440 =
             let uu____1441 = FStar_Syntax_Util.is_total_comp c in
             Prims.op_Negation uu____1441 in
           if uu____1440
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b] in
              let typ' = comp_to_typ c in
              let uu____1447 = new_uvar env' typ' in
              bind uu____1447
                (fun u  ->
                   let uu____1454 =
                     let uu____1455 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None in
                     FStar_TypeChecker_Rel.teq_nosmt
                       goal.FStar_Tactics_Types.context
                       goal.FStar_Tactics_Types.witness uu____1455 in
                   if uu____1454
                   then
                     let uu____1458 =
                       let uu____1461 =
                         let uu___98_1462 = goal in
                         let uu____1463 = bnorm env' u in
                         let uu____1464 = bnorm env' typ' in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1463;
                           FStar_Tactics_Types.goal_ty = uu____1464;
                           FStar_Tactics_Types.opts =
                             (uu___98_1462.FStar_Tactics_Types.opts)
                         } in
                       replace_cur uu____1461 in
                     bind uu____1458 (fun uu____1466  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____1472 =
             FStar_Syntax_Print.term_to_string
               goal.FStar_Tactics_Types.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1472)
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
       (let uu____1493 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty in
        match uu____1493 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1512 =
              let uu____1513 = FStar_Syntax_Util.is_total_comp c in
              Prims.op_Negation uu____1513 in
            if uu____1512
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty in
               let bs =
                 let uu____1529 = FStar_Syntax_Syntax.mk_binder bv in
                 [uu____1529; b] in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs in
               let uu____1531 =
                 let uu____1534 = comp_to_typ c in new_uvar env' uu____1534 in
               bind uu____1531
                 (fun u  ->
                    let lb =
                      let uu____1551 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____1551 in
                    let body = FStar_Syntax_Syntax.bv_to_name bv in
                    let uu____1555 =
                      FStar_Syntax_Subst.close_let_rec [lb] body in
                    match uu____1555 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos in
                        (FStar_Util.print_string "calling teq_nosmt\n";
                         (let res =
                            FStar_TypeChecker_Rel.teq_nosmt
                              goal.FStar_Tactics_Types.context
                              goal.FStar_Tactics_Types.witness tm in
                          if res
                          then
                            let uu____1593 =
                              let uu____1596 =
                                let uu___99_1597 = goal in
                                let uu____1598 = bnorm env' u in
                                let uu____1599 =
                                  let uu____1600 = comp_to_typ c in
                                  bnorm env' uu____1600 in
                                {
                                  FStar_Tactics_Types.context = env';
                                  FStar_Tactics_Types.witness = uu____1598;
                                  FStar_Tactics_Types.goal_ty = uu____1599;
                                  FStar_Tactics_Types.opts =
                                    (uu___99_1597.FStar_Tactics_Types.opts)
                                } in
                              replace_cur uu____1596 in
                            bind uu____1593
                              (fun uu____1607  ->
                                 let uu____1608 =
                                   let uu____1613 =
                                     FStar_Syntax_Syntax.mk_binder bv in
                                   (uu____1613, b) in
                                 ret uu____1608)
                          else fail "intro_rec: unification failed"))))
        | FStar_Pervasives_Native.None  ->
            let uu____1627 =
              FStar_Syntax_Print.term_to_string
                goal.FStar_Tactics_Types.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1627))
let norm: FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____1652 = FStar_TypeChecker_Normalize.tr_norm_steps s in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1652 in
         let w =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.witness in
         let t =
           normalize steps goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty in
         replace_cur
           (let uu___100_1659 = goal in
            {
              FStar_Tactics_Types.context =
                (uu___100_1659.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___100_1659.FStar_Tactics_Types.opts)
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
             let uu____1683 = FStar_TypeChecker_Normalize.tr_norm_steps s in
             FStar_List.append
               [FStar_TypeChecker_Normalize.Reify;
               FStar_TypeChecker_Normalize.UnfoldTac] uu____1683 in
           let t1 = normalize steps ps.FStar_Tactics_Types.main_context t in
           ret t1)
let istrivial: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.Simplify;
        FStar_TypeChecker_Normalize.UnfoldTac] in
      let t1 = normalize steps e t in is_true t1
let trivial: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____1705 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty in
       if uu____1705
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____1710 =
            FStar_Syntax_Print.term_to_string
              goal.FStar_Tactics_Types.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1710))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1722 =
           try
             let uu____1750 =
               (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
                 goal.FStar_Tactics_Types.context t in
             ret uu____1750
           with
           | e ->
               let uu____1777 = FStar_Syntax_Print.term_to_string t in
               let uu____1778 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1777
                 uu____1778 in
         bind uu____1722
           (fun uu____1796  ->
              match uu____1796 with
              | (t1,typ,guard) ->
                  let uu____1808 =
                    let uu____1809 =
                      let uu____1810 =
                        FStar_TypeChecker_Rel.discharge_guard
                          goal.FStar_Tactics_Types.context guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1810 in
                    Prims.op_Negation uu____1809 in
                  if uu____1808
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1814 =
                       FStar_TypeChecker_Rel.teq_nosmt
                         goal.FStar_Tactics_Types.context typ
                         goal.FStar_Tactics_Types.goal_ty in
                     if uu____1814
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1819 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1820 =
                          let uu____1821 =
                            bnorm goal.FStar_Tactics_Types.context typ in
                          FStar_Syntax_Print.term_to_string uu____1821 in
                        let uu____1822 =
                          FStar_Syntax_Print.term_to_string
                            goal.FStar_Tactics_Types.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1819 uu____1820 uu____1822))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1834 =
           try
             let uu____1862 =
               FStar_TypeChecker_TcTerm.tc_term
                 goal.FStar_Tactics_Types.context t in
             ret uu____1862
           with
           | e ->
               let uu____1889 = FStar_Syntax_Print.term_to_string t in
               let uu____1890 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1889
                 uu____1890 in
         bind uu____1834
           (fun uu____1908  ->
              match uu____1908 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1926 =
                       let uu____1927 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1927 in
                     if uu____1926
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1931 =
                          let uu____1940 =
                            let uu____1949 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1949.FStar_Syntax_Syntax.effect_args in
                          match uu____1940 with
                          | pre::post::uu____1960 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2001 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1931 with
                        | (pre,post) ->
                            let uu____2030 =
                              FStar_TypeChecker_Rel.teq_nosmt
                                goal.FStar_Tactics_Types.context post
                                goal.FStar_Tactics_Types.goal_ty in
                            if uu____2030
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____2035  ->
                                    add_irrelevant_goal
                                      goal.FStar_Tactics_Types.context pre
                                      goal.FStar_Tactics_Types.opts))
                            else
                              (let uu____2037 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____2038 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____2039 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.FStar_Tactics_Types.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2037 uu____2038 uu____2039)))))
let uvar_free_in_goal:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____2051 =
          let uu____2058 =
            FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty in
          FStar_Util.set_elements uu____2058 in
        FStar_List.map FStar_Pervasives_Native.fst uu____2051 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free:
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
exception NoUnif
let uu___is_NoUnif: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2085 -> false
let rec __apply:
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2105 = let uu____2110 = exact tm in trytac uu____2110 in
             bind uu____2105
               (fun r  ->
                  match r with
                  | FStar_Pervasives_Native.Some r1 -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2123 = FStar_Syntax_Util.arrow_one typ in
                      (match uu____2123 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           let uu____2153 =
                             let uu____2154 =
                               FStar_Syntax_Util.is_total_comp c in
                             Prims.op_Negation uu____2154 in
                           if uu____2153
                           then fail "apply: not total codomain"
                           else
                             (let uu____2158 =
                                new_uvar goal.FStar_Tactics_Types.context
                                  bv.FStar_Syntax_Syntax.sort in
                              bind uu____2158
                                (fun u  ->
                                   let tm' =
                                     FStar_Syntax_Syntax.mk_Tm_app tm
                                       [(u, aq)] FStar_Pervasives_Native.None
                                       (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                   let typ' =
                                     let uu____2178 = comp_to_typ c in
                                     FStar_All.pipe_left
                                       (FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.NT (bv, u)])
                                       uu____2178 in
                                   let uu____2179 = __apply uopt tm' typ' in
                                   bind uu____2179
                                     (fun uu____2186  ->
                                        let uu____2187 =
                                          let uu____2188 =
                                            let uu____2191 =
                                              let uu____2192 =
                                                FStar_Syntax_Util.head_and_args
                                                  u in
                                              FStar_Pervasives_Native.fst
                                                uu____2192 in
                                            FStar_Syntax_Subst.compress
                                              uu____2191 in
                                          uu____2188.FStar_Syntax_Syntax.n in
                                        match uu____2187 with
                                        | FStar_Syntax_Syntax.Tm_uvar
                                            (uvar,uu____2220) ->
                                            bind get
                                              (fun ps  ->
                                                 let uu____2248 =
                                                   uopt &&
                                                     (uvar_free uvar ps) in
                                                 if uu____2248
                                                 then ret ()
                                                 else
                                                   (let uu____2252 =
                                                      let uu____2255 =
                                                        let uu____2256 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            u in
                                                        let uu____2257 =
                                                          bnorm
                                                            goal.FStar_Tactics_Types.context
                                                            bv.FStar_Syntax_Syntax.sort in
                                                        {
                                                          FStar_Tactics_Types.context
                                                            =
                                                            (goal.FStar_Tactics_Types.context);
                                                          FStar_Tactics_Types.witness
                                                            = uu____2256;
                                                          FStar_Tactics_Types.goal_ty
                                                            = uu____2257;
                                                          FStar_Tactics_Types.opts
                                                            =
                                                            (goal.FStar_Tactics_Types.opts)
                                                        } in
                                                      [uu____2255] in
                                                    add_goals uu____2252))
                                        | uu____2258 -> ret ()))))))
let try_unif: 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
let apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2315 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               goal.FStar_Tactics_Types.context tm in
           match uu____2315 with
           | (tm1,typ,guard) ->
               let uu____2327 =
                 let uu____2328 =
                   let uu____2329 =
                     FStar_TypeChecker_Rel.discharge_guard
                       goal.FStar_Tactics_Types.context guard in
                   FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                     uu____2329 in
                 Prims.op_Negation uu____2328 in
               if uu____2327
               then fail "apply: got non-trivial guard"
               else
                 (let uu____2333 =
                    let uu____2336 = __apply uopt tm1 typ in focus uu____2336 in
                  let uu____2339 =
                    let uu____2342 = FStar_Syntax_Print.term_to_string tm1 in
                    let uu____2343 = FStar_Syntax_Print.term_to_string typ in
                    let uu____2344 =
                      FStar_Syntax_Print.term_to_string
                        goal.FStar_Tactics_Types.goal_ty in
                    fail3
                      "apply: Cannot instantiate %s (of type %s) to match goal (%s)"
                      uu____2342 uu____2343 uu____2344 in
                  try_unif uu____2333 uu____2339))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let is_unit_t t =
      let uu____2357 =
        let uu____2358 = FStar_Syntax_Subst.compress t in
        uu____2358.FStar_Syntax_Syntax.n in
      match uu____2357 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
          true
      | uu____2362 -> false in
    bind cur_goal
      (fun goal  ->
         let uu____2370 =
           (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
             goal.FStar_Tactics_Types.context tm in
         match uu____2370 with
         | (tm1,t,guard) ->
             let uu____2382 =
               let uu____2383 =
                 let uu____2384 =
                   FStar_TypeChecker_Rel.discharge_guard
                     goal.FStar_Tactics_Types.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____2384 in
               Prims.op_Negation uu____2383 in
             if uu____2382
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____2388 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____2388 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2418 =
                         FStar_List.fold_left
                           (fun uu____2464  ->
                              fun uu____2465  ->
                                match (uu____2464, uu____2465) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2568 = is_unit_t b_t in
                                    if uu____2568
                                    then
                                      (((FStar_Syntax_Util.exp_unit, aq) ::
                                        uvs), guard1,
                                        ((FStar_Syntax_Syntax.NT
                                            (b, FStar_Syntax_Util.exp_unit))
                                        :: subst1))
                                    else
                                      (let uu____2606 =
                                         FStar_TypeChecker_Util.new_implicit_var
                                           "apply_lemma"
                                           (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                           goal.FStar_Tactics_Types.context
                                           b_t in
                                       match uu____2606 with
                                       | (u,uu____2636,g_u) ->
                                           let uu____2650 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               guard1 g_u in
                                           (((u, aq) :: uvs), uu____2650,
                                             ((FStar_Syntax_Syntax.NT (b, u))
                                             :: subst1)))) ([], guard, []) bs in
                       match uu____2418 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____2720 =
                             let uu____2729 =
                               let uu____2738 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____2738.FStar_Syntax_Syntax.effect_args in
                             match uu____2729 with
                             | pre::post::uu____2749 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____2790 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____2720 with
                            | (pre,post) ->
                                let uu____2819 =
                                  let uu____2822 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.FStar_Tactics_Types.context
                                    uu____2822
                                    goal.FStar_Tactics_Types.goal_ty in
                                (match uu____2819 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____2825 =
                                       let uu____2826 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____2826 in
                                     let uu____2827 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.FStar_Tactics_Types.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____2825 uu____2827
                                 | FStar_Pervasives_Native.Some g ->
                                     let uu____2829 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         goal.FStar_Tactics_Types.context g in
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____2900  ->
                                               match uu____2900 with
                                               | (uu____2913,uu____2914,uu____2915,tm2,uu____2917,uu____2918)
                                                   ->
                                                   let uu____2919 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____2919 with
                                                    | (hd1,uu____2935) ->
                                                        let uu____2956 =
                                                          let uu____2957 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____2957.FStar_Syntax_Syntax.n in
                                                        (match uu____2956
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____2960 ->
                                                             true
                                                         | uu____2977 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let uu____2979 =
                                         add_implicits implicits1 in
                                       bind uu____2979
                                         (fun uu____2983  ->
                                            bind dismiss
                                              (fun uu____2992  ->
                                                 let is_free_uvar uv t1 =
                                                   let free_uvars =
                                                     let uu____3003 =
                                                       let uu____3010 =
                                                         FStar_Syntax_Free.uvars
                                                           t1 in
                                                       FStar_Util.set_elements
                                                         uu____3010 in
                                                     FStar_List.map
                                                       FStar_Pervasives_Native.fst
                                                       uu____3003 in
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
                                                   let uu____3051 =
                                                     FStar_Syntax_Util.head_and_args
                                                       t1 in
                                                   match uu____3051 with
                                                   | (hd1,uu____3067) ->
                                                       (match hd1.FStar_Syntax_Syntax.n
                                                        with
                                                        | FStar_Syntax_Syntax.Tm_uvar
                                                            (uv,uu____3089)
                                                            ->
                                                            appears uv goals
                                                        | uu____3114 -> false) in
                                                 let sub_goals =
                                                   FStar_All.pipe_right
                                                     implicits1
                                                     (FStar_List.map
                                                        (fun uu____3155  ->
                                                           match uu____3155
                                                           with
                                                           | (_msg,_env,_uvar,term,typ,uu____3173)
                                                               ->
                                                               let uu____3174
                                                                 =
                                                                 bnorm
                                                                   goal.FStar_Tactics_Types.context
                                                                   term in
                                                               let uu____3175
                                                                 =
                                                                 bnorm
                                                                   goal.FStar_Tactics_Types.context
                                                                   typ in
                                                               {
                                                                 FStar_Tactics_Types.context
                                                                   =
                                                                   (goal.FStar_Tactics_Types.context);
                                                                 FStar_Tactics_Types.witness
                                                                   =
                                                                   uu____3174;
                                                                 FStar_Tactics_Types.goal_ty
                                                                   =
                                                                   uu____3175;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (goal.FStar_Tactics_Types.opts)
                                                               })) in
                                                 let rec filter' f xs =
                                                   match xs with
                                                   | [] -> []
                                                   | x::xs1 ->
                                                       let uu____3213 =
                                                         f x xs1 in
                                                       if uu____3213
                                                       then
                                                         let uu____3216 =
                                                           filter' f xs1 in
                                                         x :: uu____3216
                                                       else filter' f xs1 in
                                                 let sub_goals1 =
                                                   filter'
                                                     (fun g1  ->
                                                        fun goals  ->
                                                          let uu____3230 =
                                                            checkone
                                                              g1.FStar_Tactics_Types.witness
                                                              goals in
                                                          Prims.op_Negation
                                                            uu____3230)
                                                     sub_goals in
                                                 let uu____3231 =
                                                   add_irrelevant_goal
                                                     goal.FStar_Tactics_Types.context
                                                     pre
                                                     goal.FStar_Tactics_Types.opts in
                                                 bind uu____3231
                                                   (fun uu____3236  ->
                                                      let uu____3237 =
                                                        trytac trivial in
                                                      bind uu____3237
                                                        (fun uu____3245  ->
                                                           add_goals
                                                             sub_goals1)))))))))))
let destruct_eq':
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3264 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____3264 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____3274::(e1,uu____3276)::(e2,uu____3278)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____3337 -> FStar_Pervasives_Native.None
let destruct_eq:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____3360 = destruct_eq' typ in
    match uu____3360 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____3390 = FStar_Syntax_Util.un_squash typ in
        (match uu____3390 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3423 =
           FStar_All.pipe_left mlog
             (fun uu____3433  ->
                let uu____3434 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____3435 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3434
                  uu____3435) in
         bind uu____3423
           (fun uu____3443  ->
              let uu____3444 =
                let uu____3451 =
                  let uu____3452 =
                    FStar_TypeChecker_Env.lookup_bv
                      goal.FStar_Tactics_Types.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3452 in
                destruct_eq uu____3451 in
              match uu____3444 with
              | FStar_Pervasives_Native.Some (x,e) ->
                  let uu____3469 =
                    let uu____3470 = FStar_Syntax_Subst.compress x in
                    uu____3470.FStar_Syntax_Syntax.n in
                  (match uu____3469 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___107_3477 = goal in
                         let uu____3478 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)]
                             goal.FStar_Tactics_Types.witness in
                         let uu____3479 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)]
                             goal.FStar_Tactics_Types.goal_ty in
                         {
                           FStar_Tactics_Types.context =
                             (uu___107_3477.FStar_Tactics_Types.context);
                           FStar_Tactics_Types.witness = uu____3478;
                           FStar_Tactics_Types.goal_ty = uu____3479;
                           FStar_Tactics_Types.opts =
                             (uu___107_3477.FStar_Tactics_Types.opts)
                         } in
                       replace_cur goal1
                   | uu____3480 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3481 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3493 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____3493 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty in
           let uu____3515 = FStar_Util.set_mem x fns_ty in
           if uu____3515
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____3519 = new_uvar env' goal.FStar_Tactics_Types.goal_ty in
              bind uu____3519
                (fun u  ->
                   let uu____3525 =
                     let uu____3526 =
                       FStar_TypeChecker_Rel.teq_nosmt
                         goal.FStar_Tactics_Types.context
                         goal.FStar_Tactics_Types.witness u in
                     Prims.op_Negation uu____3526 in
                   if uu____3525
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___108_3531 = goal in
                        let uu____3532 = bnorm env' u in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____3532;
                          FStar_Tactics_Types.goal_ty =
                            (uu___108_3531.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___108_3531.FStar_Tactics_Types.opts)
                        } in
                      bind dismiss (fun uu____3534  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3546 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____3546 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3573 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
       match uu____3573 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____3595 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____3595 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___109_3629 = goal in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___109_3629.FStar_Tactics_Types.opts)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3641 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context in
         match uu____3641 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____3662 = FStar_Syntax_Print.bv_to_string x in
               let uu____3663 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____3662 uu____3663
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____3681 = revert_all_hd xs1 in
        bind uu____3681 (fun uu____3685  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___110_3702 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___110_3702.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___110_3702.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___110_3702.FStar_Tactics_Types.opts)
           } in
         bind dismiss (fun uu____3704  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___111_3721 = g in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___111_3721.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___111_3721.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___111_3721.FStar_Tactics_Types.opts)
           } in
         bind dismiss (fun uu____3723  -> add_goals [g']))
let rec mapM: 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3765 = f x in
          bind uu____3765
            (fun y  ->
               let uu____3773 = mapM f xs in
               bind uu____3773 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____3819 = FStar_Syntax_Subst.compress t in
          uu____3819.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____3854 = ff hd1 in
              bind uu____3854
                (fun hd2  ->
                   let fa uu____3874 =
                     match uu____3874 with
                     | (a,q) ->
                         let uu____3887 = ff a in
                         bind uu____3887 (fun a1  -> ret (a1, q)) in
                   let uu____3900 = mapM fa args in
                   bind uu____3900
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____3960 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____3960 with
               | (bs1,t') ->
                   let uu____3969 =
                     let uu____3972 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____3972 t' in
                   bind uu____3969
                     (fun t''  ->
                        let uu____3976 =
                          let uu____3977 =
                            let uu____3994 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____3995 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____3994, uu____3995, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____3977 in
                        ret uu____3976))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4016 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___112_4020 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___112_4020.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___112_4020.FStar_Syntax_Syntax.vars)
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
            let uu____4049 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____4049 with
            | (t1,lcomp,g) ->
                let uu____4061 =
                  (let uu____4064 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____4064) ||
                    (let uu____4066 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____4066) in
                if uu____4061
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____4073 = new_uvar env typ in
                   bind uu____4073
                     (fun ut  ->
                        log ps
                          (fun uu____4084  ->
                             let uu____4085 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____4086 =
                               FStar_Syntax_Print.term_to_string ut in
                             FStar_Util.print2
                               "Pointwise_rec: making equality %s = %s\n"
                               uu____4085 uu____4086);
                        (let uu____4087 =
                           let uu____4090 =
                             let uu____4091 =
                               FStar_TypeChecker_TcTerm.universe_of env typ in
                             FStar_Syntax_Util.mk_eq2 uu____4091 typ t1 ut in
                           add_irrelevant_goal env uu____4090 opts in
                         bind uu____4087
                           (fun uu____4094  ->
                              let uu____4095 =
                                bind tau
                                  (fun uu____4100  ->
                                     let ut1 =
                                       FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                         env ut in
                                     ret ut1) in
                              focus uu____4095))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4121 =
           match ps.FStar_Tactics_Types.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____4121 with
         | (g,gs) ->
             let gt1 = g.FStar_Tactics_Types.goal_ty in
             (log ps
                (fun uu____4158  ->
                   let uu____4159 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4159);
              bind dismiss_all
                (fun uu____4162  ->
                   let uu____4163 =
                     tac_bottom_fold_env
                       (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                       g.FStar_Tactics_Types.context gt1 in
                   bind uu____4163
                     (fun gt'  ->
                        log ps
                          (fun uu____4173  ->
                             let uu____4174 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4174);
                        (let uu____4175 = push_goals gs in
                         bind uu____4175
                           (fun uu____4179  ->
                              add_goals
                                [(let uu___113_4181 = g in
                                  {
                                    FStar_Tactics_Types.context =
                                      (uu___113_4181.FStar_Tactics_Types.context);
                                    FStar_Tactics_Types.witness =
                                      (uu___113_4181.FStar_Tactics_Types.witness);
                                    FStar_Tactics_Types.goal_ty = gt';
                                    FStar_Tactics_Types.opts =
                                      (uu___113_4181.FStar_Tactics_Types.opts)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4201 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty in
       match uu____4201 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4213 = FStar_Syntax_Util.head_and_args' t in
           (match uu____4213 with
            | (hd1,args) ->
                let uu____4246 =
                  let uu____4259 =
                    let uu____4260 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____4260.FStar_Syntax_Syntax.n in
                  (uu____4259, args) in
                (match uu____4246 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4274::(l,uu____4276)::(r,uu____4278)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4325 =
                       let uu____4326 =
                         FStar_TypeChecker_Rel.teq_nosmt
                           g.FStar_Tactics_Types.context l r in
                       Prims.op_Negation uu____4326 in
                     if uu____4325
                     then
                       let uu____4329 = FStar_Syntax_Print.term_to_string l in
                       let uu____4330 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4329 uu____4330
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____4334) ->
                     let uu____4351 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____4351))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4359 =
         new_uvar g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty in
       bind uu____4359
         (fun u  ->
            let g' =
              let uu___114_4366 = g in
              {
                FStar_Tactics_Types.context =
                  (uu___114_4366.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___114_4366.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___114_4366.FStar_Tactics_Types.opts)
              } in
            bind dismiss
              (fun uu____4369  ->
                 let uu____4370 =
                   let uu____4373 =
                     let uu____4374 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty in
                     FStar_Syntax_Util.mk_eq2 uu____4374
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness in
                   add_irrelevant_goal g.FStar_Tactics_Types.context
                     uu____4373 g.FStar_Tactics_Types.opts in
                 bind uu____4370
                   (fun uu____4377  ->
                      let uu____4378 = add_goals [g'] in
                      bind uu____4378 (fun uu____4382  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___115_4399 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___115_4399.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___115_4399.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___115_4399.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___115_4399.FStar_Tactics_Types.smt_goals)
              })
       | uu____4400 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___116_4415 = ps in
              {
                FStar_Tactics_Types.main_context =
                  (uu___116_4415.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___116_4415.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___116_4415.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___116_4415.FStar_Tactics_Types.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____4422 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____4464 =
           (g.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
             g.FStar_Tactics_Types.context t in
         match uu____4464 with
         | (t1,typ,guard) ->
             let uu____4480 = FStar_Syntax_Util.head_and_args typ in
             (match uu____4480 with
              | (hd1,args) ->
                  let uu____4523 =
                    let uu____4536 =
                      let uu____4537 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____4537.FStar_Syntax_Syntax.n in
                    (uu____4536, args) in
                  (match uu____4523 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____4556)::(q,uu____4558)::[]) when
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
                         let uu___117_4596 = g in
                         let uu____4597 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_p in
                         {
                           FStar_Tactics_Types.context = uu____4597;
                           FStar_Tactics_Types.witness =
                             (uu___117_4596.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___117_4596.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___117_4596.FStar_Tactics_Types.opts)
                         } in
                       let g2 =
                         let uu___118_4599 = g in
                         let uu____4600 =
                           FStar_TypeChecker_Env.push_bv
                             g.FStar_Tactics_Types.context v_q in
                         {
                           FStar_Tactics_Types.context = uu____4600;
                           FStar_Tactics_Types.witness =
                             (uu___118_4599.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___118_4599.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___118_4599.FStar_Tactics_Types.opts)
                         } in
                       bind dismiss
                         (fun uu____4607  ->
                            let uu____4608 = add_goals [g1; g2] in
                            bind uu____4608
                              (fun uu____4617  ->
                                 let uu____4618 =
                                   let uu____4623 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____4624 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____4623, uu____4624) in
                                 ret uu____4618))
                   | uu____4629 ->
                       let uu____4642 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____4642)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____4665 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
          FStar_Options.set uu____4665);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___119_4672 = g in
                 {
                   FStar_Tactics_Types.context =
                     (uu___119_4672.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___119_4672.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___119_4672.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts'
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
           let uu____4713 =
             (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.type_of
               env tm in
           match uu____4713 with
           | (tm1,typ,guard) ->
               (FStar_TypeChecker_Rel.force_trivial_guard env guard; ret tm1))
let uvar_env:
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____4742 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____4748 =
              let uu____4749 = FStar_Syntax_Util.type_u () in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4749 in
            new_uvar env uu____4748 in
      bind uu____4742
        (fun typ  ->
           let uu____4761 = new_uvar env typ in
           bind uu____4761 (fun t  -> ret t))
let unify:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____4781 =
             FStar_TypeChecker_Rel.teq_nosmt
               ps.FStar_Tactics_Types.main_context t1 t2 in
           ret uu____4781)
let launch_process:
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____4801  ->
             let uu____4802 = FStar_Options.unsafe_tactic_exec () in
             if uu____4802
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____4808  -> fun uu____4809  -> false) in
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
      let uu____4831 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____4831 with
      | (u,uu____4849,g_u) ->
          let g =
            let uu____4864 = FStar_Options.peek () in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____4864
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
      let uu____4881 = goal_of_goal_ty env typ in
      match uu____4881 with
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