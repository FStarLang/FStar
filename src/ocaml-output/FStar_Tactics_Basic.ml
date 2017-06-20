open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let bnorm:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun e  -> fun t  -> FStar_TypeChecker_Normalize.normalize [] e t
type goal =
  {
  context: env;
  witness: FStar_Syntax_Syntax.term;
  goal_ty: FStar_Syntax_Syntax.typ;}
type proofstate =
  {
  main_context: env;
  main_goal: goal;
  all_implicits: implicits;
  goals: goal Prims.list;
  smt_goals: goal Prims.list;}
type 'a result =
  | Success of ('a* proofstate)
  | Failed of (Prims.string* proofstate)
let uu___is_Success projectee =
  match projectee with | Success _0 -> true | uu____118 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success _0 -> _0
let uu___is_Failed projectee =
  match projectee with | Failed _0 -> true | uu____153 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed _0 -> _0
exception TacFailure of Prims.string
let uu___is_TacFailure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | TacFailure uu____181 -> true | uu____182 -> false
let __proj__TacFailure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | TacFailure uu____190 -> uu____190
type 'a tac = {
  tac_f: proofstate -> 'a result;}
let mk_tac f = { tac_f = f }
let run t p = t.tac_f p
let ret x = mk_tac (fun p  -> Success (x, p))
let bind t1 t2 =
  mk_tac
    (fun p  ->
       let uu____299 = run t1 p in
       match uu____299 with
       | Success (a,q) -> let uu____304 = t2 a in run uu____304 q
       | Failed (msg,q) -> Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____314 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____314
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____315 = FStar_Syntax_Print.term_to_string g.witness in
    let uu____316 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____315 uu____316
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____329 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____329
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____342 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____342
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____359 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____359
let comp_to_typ:
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____365) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____373) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: goal -> Prims.bool =
  fun g  ->
    let uu____385 = FStar_Syntax_Util.un_squash g.goal_ty in
    match uu____385 with | Some t -> true | uu____394 -> false
let dump_goal ps goal =
  let uu____414 = goal_to_string goal in tacprint uu____414
let dump_cur: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____424 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____427 = FStar_List.hd ps.goals in dump_goal ps uu____427))
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____439 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____439);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____448 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____448);
      FStar_List.iter (dump_goal ps) ps.smt_goals
let print_proof_state1: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_cur p msg; Success ((), p))
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let tac_verb_dbg: Prims.bool option FStar_ST.ref = FStar_Util.mk_ref None
let rec log: proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun ps  ->
    fun f  ->
      let uu____492 = FStar_ST.read tac_verb_dbg in
      match uu____492 with
      | None  ->
          ((let uu____498 =
              let uu____500 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              Some uu____500 in
            FStar_ST.write tac_verb_dbg uu____498);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____529 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____529
        then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
        else ());
       Failed (msg, ps))
let fail1 msg x = let uu____547 = FStar_Util.format1 msg x in fail uu____547
let fail2 msg x y =
  let uu____570 = FStar_Util.format2 msg x y in fail uu____570
let fail3 msg x y z =
  let uu____599 = FStar_Util.format3 msg x y z in fail uu____599
let trytac t =
  mk_tac
    (fun ps  ->
       let tx = FStar_Syntax_Unionfind.new_transaction () in
       let uu____616 = run t ps in
       match uu____616 with
       | Success (a,q) ->
           (FStar_Syntax_Unionfind.commit tx; Success ((Some a), q))
       | Failed (uu____625,uu____626) ->
           (FStar_Syntax_Unionfind.rollback tx; Success (None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____636  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____645 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____645
      then ()
      else
        (let uu____647 =
           let uu____648 =
             let uu____649 = FStar_Syntax_Print.term_to_string solution in
             let uu____650 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____651 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____649
               uu____650 uu____651 in
           TacFailure uu____648 in
         raise uu____647)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____654 =
         let uu___79_655 = p in
         let uu____656 = FStar_List.tl p.goals in
         {
           main_context = (uu___79_655.main_context);
           main_goal = (uu___79_655.main_goal);
           all_implicits = (uu___79_655.all_implicits);
           goals = uu____656;
           smt_goals = (uu___79_655.smt_goals)
         } in
       set uu____654)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___80_660 = p in
          {
            main_context = (uu___80_660.main_context);
            main_goal = (uu___80_660.main_goal);
            all_implicits = (uu___80_660.all_implicits);
            goals = [];
            smt_goals = (uu___80_660.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_670 = p in
            {
              main_context = (uu___81_670.main_context);
              main_goal = (uu___81_670.main_goal);
              all_implicits = (uu___81_670.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___81_670.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_680 = p in
            {
              main_context = (uu___82_680.main_context);
              main_goal = (uu___82_680.main_goal);
              all_implicits = (uu___82_680.all_implicits);
              goals = (uu___82_680.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_690 = p in
            {
              main_context = (uu___83_690.main_context);
              main_goal = (uu___83_690.main_goal);
              all_implicits = (uu___83_690.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___83_690.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_700 = p in
            {
              main_context = (uu___84_700.main_context);
              main_goal = (uu___84_700.main_goal);
              all_implicits = (uu___84_700.all_implicits);
              goals = (uu___84_700.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____707  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___85_715 = p in
            {
              main_context = (uu___85_715.main_context);
              main_goal = (uu___85_715.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___85_715.goals);
              smt_goals = (uu___85_715.smt_goals)
            }))
let add_irrelevant_goal: env -> FStar_Syntax_Syntax.typ -> Prims.unit tac =
  fun env  ->
    fun phi  ->
      let typ = FStar_Syntax_Util.mk_squash phi in
      let uu____735 =
        FStar_TypeChecker_Util.new_implicit_var "add_irrelevant_goal"
          phi.FStar_Syntax_Syntax.pos env typ in
      match uu____735 with
      | (u,uu____744,g_u) ->
          let goal = { context = env; witness = u; goal_ty = typ } in
          let uu____753 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____753 (fun uu____755  -> add_goals [goal])
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____760 = FStar_Syntax_Util.un_squash t in
    match uu____760 with
    | Some t' ->
        let uu____769 =
          let uu____770 = FStar_Syntax_Subst.compress t' in
          uu____770.FStar_Syntax_Syntax.n in
        (match uu____769 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____774 -> false)
    | uu____775 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____783 = FStar_Syntax_Util.un_squash t in
    match uu____783 with
    | Some t' ->
        let uu____792 =
          let uu____793 = FStar_Syntax_Subst.compress t' in
          uu____793.FStar_Syntax_Syntax.n in
        (match uu____792 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____797 -> false)
    | uu____798 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____810 = is_irrelevant g in
       if uu____810
       then bind dismiss (fun uu____812  -> add_smt_goals [g])
       else
         (let uu____814 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____814))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____849 =
         try let uu____866 = FStar_List.splitAt n1 p.goals in ret uu____866
         with | uu____881 -> fail "divide: not enough goals" in
       bind uu____849
         (fun uu____892  ->
            match uu____892 with
            | (lgs,rgs) ->
                let lp =
                  let uu___86_907 = p in
                  {
                    main_context = (uu___86_907.main_context);
                    main_goal = (uu___86_907.main_goal);
                    all_implicits = (uu___86_907.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___87_909 = p in
                  {
                    main_context = (uu___87_909.main_context);
                    main_goal = (uu___87_909.main_goal);
                    all_implicits = (uu___87_909.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____910 = set lp in
                bind uu____910
                  (fun uu____914  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____921 = set rp in
                               bind uu____921
                                 (fun uu____925  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___88_933 = p in
                                                {
                                                  main_context =
                                                    (uu___88_933.main_context);
                                                  main_goal =
                                                    (uu___88_933.main_goal);
                                                  all_implicits =
                                                    (uu___88_933.all_implicits);
                                                  goals =
                                                    (FStar_List.append
                                                       lp'.goals rp'.goals);
                                                  smt_goals =
                                                    (FStar_List.append
                                                       lp'.smt_goals
                                                       (FStar_List.append
                                                          rp'.smt_goals
                                                          p.smt_goals))
                                                } in
                                              let uu____934 = set p' in
                                              bind uu____934
                                                (fun uu____938  -> ret (a, b))))))))))
let focus_cur_goal f =
  let uu____953 = divide (Prims.parse_int "1") f idtac in
  bind uu____953 (fun uu____959  -> match uu____959 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____982::uu____983 ->
           let uu____985 =
             let uu____990 = map tau in
             divide (Prims.parse_int "1") tau uu____990 in
           bind uu____985
             (fun uu____998  -> match uu____998 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1023 =
        bind t1
          (fun uu____1025  ->
             let uu____1026 = map t2 in
             bind uu____1026 (fun uu____1030  -> ret ())) in
      focus_cur_goal uu____1023
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____1038 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1038 with
       | Some (b,c) ->
           let uu____1049 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1049 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1069 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1072 =
                  let uu____1073 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1073 in
                if uu____1072
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1086 =
                     FStar_TypeChecker_Util.new_implicit_var "intro"
                       typ'.FStar_Syntax_Syntax.pos env' typ' in
                   match uu____1086 with
                   | (u,uu____1097,g) ->
                       let uu____1105 =
                         let uu____1106 = FStar_Syntax_Util.abs [b1] u None in
                         FStar_TypeChecker_Rel.teq_nosmt goal.context
                           goal.witness uu____1106 in
                       if uu____1105
                       then
                         let g1 =
                           let uu____1115 =
                             FStar_TypeChecker_Rel.solve_deferred_constraints
                               goal.context g in
                           FStar_All.pipe_right uu____1115
                             FStar_TypeChecker_Rel.resolve_implicits in
                         let uu____1116 =
                           add_implicits g1.FStar_TypeChecker_Env.implicits in
                         bind uu____1116
                           (fun uu____1120  ->
                              let uu____1121 =
                                let uu____1123 =
                                  let uu___91_1124 = goal in
                                  let uu____1125 = bnorm env' u in
                                  let uu____1126 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1125;
                                    goal_ty = uu____1126
                                  } in
                                replace_cur uu____1123 in
                              bind uu____1121 (fun uu____1129  -> ret b1))
                       else fail "intro: unification failed"))
       | None  ->
           let uu____1137 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1137)
let norm: FStar_Reflection_Data.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let tr s1 =
           match s1 with
           | FStar_Reflection_Data.Simpl  ->
               [FStar_TypeChecker_Normalize.Simplify]
           | FStar_Reflection_Data.WHNF  ->
               [FStar_TypeChecker_Normalize.WHNF]
           | FStar_Reflection_Data.Primops  ->
               [FStar_TypeChecker_Normalize.Primops]
           | FStar_Reflection_Data.Delta  ->
               [FStar_TypeChecker_Normalize.UnfoldUntil
                  FStar_Syntax_Syntax.Delta_constant] in
         let steps =
           let uu____1157 =
             let uu____1159 = FStar_List.map tr s in
             FStar_List.flatten uu____1159 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1157 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___92_1165 = goal in
            { context = (uu___92_1165.context); witness = w; goal_ty = t }))
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
      let t1 = FStar_TypeChecker_Normalize.normalize steps e t in is_true t1
let trivial: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____1179 = istrivial goal.context goal.goal_ty in
       if uu____1179
       then (solve goal FStar_Syntax_Const.exp_unit; dismiss)
       else
         (let uu____1183 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1183))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1191 =
           try
             let uu____1205 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1205
           with
           | e ->
               let uu____1218 = FStar_Syntax_Print.term_to_string t in
               let uu____1219 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1218
                 uu____1219 in
         bind uu____1191
           (fun uu____1226  ->
              match uu____1226 with
              | (t1,typ,guard) ->
                  let uu____1234 =
                    let uu____1235 =
                      let uu____1236 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1236 in
                    Prims.op_Negation uu____1235 in
                  if uu____1234
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1239 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1239
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1243 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1244 =
                          let uu____1245 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1245 in
                        let uu____1246 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1243 uu____1244 uu____1246))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1254 =
           try
             let uu____1268 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1268
           with
           | e ->
               let uu____1281 = FStar_Syntax_Print.term_to_string t in
               let uu____1282 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1281
                 uu____1282 in
         bind uu____1254
           (fun uu____1289  ->
              match uu____1289 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1302 =
                       let uu____1303 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1303 in
                     if uu____1302
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1306 =
                          let uu____1313 =
                            let uu____1319 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1319.FStar_Syntax_Syntax.effect_args in
                          match uu____1313 with
                          | pre::post::uu____1328 -> ((fst pre), (fst post))
                          | uu____1358 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1306 with
                        | (pre,post) ->
                            let uu____1381 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1381
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1384  ->
                                    add_irrelevant_goal goal.context pre))
                            else
                              (let uu____1386 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1387 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1388 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1386 uu____1387 uu____1388)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1399 =
          let uu____1403 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1403 in
        FStar_List.map FStar_Pervasives.fst uu____1399 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1430 = let uu____1433 = exact tm in trytac uu____1433 in
           bind uu____1430
             (fun r  ->
                match r with
                | Some r1 -> ret ()
                | None  ->
                    let uu____1440 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1440 with
                     | (tm1,typ,guard) ->
                         let uu____1448 =
                           let uu____1449 =
                             let uu____1450 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1450 in
                           Prims.op_Negation uu____1449 in
                         if uu____1448
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1453 = FStar_Syntax_Util.arrow_one typ in
                            match uu____1453 with
                            | None  ->
                                let uu____1460 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1460
                            | Some ((bv,aq),c) ->
                                let uu____1470 =
                                  let uu____1471 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____1471 in
                                if uu____1470
                                then fail "apply: not total"
                                else
                                  (let uu____1474 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   match uu____1474 with
                                   | (u,uu____1483,g_u) ->
                                       let tm' =
                                         FStar_Syntax_Syntax.mk_Tm_app tm1
                                           [(u, aq)] None
                                           (goal.context).FStar_TypeChecker_Env.range in
                                       let uu____1500 = __apply uopt tm' in
                                       bind uu____1500
                                         (fun uu____1502  ->
                                            let g_u1 =
                                              let uu____1504 =
                                                FStar_TypeChecker_Rel.solve_deferred_constraints
                                                  goal.context g_u in
                                              FStar_All.pipe_right uu____1504
                                                FStar_TypeChecker_Rel.resolve_implicits in
                                            let uu____1505 =
                                              let uu____1506 =
                                                let uu____1509 =
                                                  let uu____1510 =
                                                    FStar_Syntax_Util.head_and_args
                                                      u in
                                                  fst uu____1510 in
                                                FStar_Syntax_Subst.compress
                                                  uu____1509 in
                                              uu____1506.FStar_Syntax_Syntax.n in
                                            match uu____1505 with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                (uvar,uu____1529) ->
                                                let uu____1542 =
                                                  add_implicits
                                                    g_u1.FStar_TypeChecker_Env.implicits in
                                                bind uu____1542
                                                  (fun uu____1544  ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1546 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____1546
                                                          then ret ()
                                                          else
                                                            (let uu____1549 =
                                                               let uu____1551
                                                                 =
                                                                 let uu____1552
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____1553
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1552;
                                                                   goal_ty =
                                                                    uu____1553
                                                                 } in
                                                               [uu____1551] in
                                                             add_goals
                                                               uu____1549)))
                                            | uu____1554 -> ret ()))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1561 = __apply true tm in focus_cur_goal uu____1561
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1570 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1570 with
         | (tm1,t,guard) ->
             let uu____1578 =
               let uu____1579 =
                 let uu____1580 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1580 in
               Prims.op_Negation uu____1579 in
             if uu____1578
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1583 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____1583 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____1600 =
                         FStar_List.fold_left
                           (fun uu____1617  ->
                              fun uu____1618  ->
                                match (uu____1617, uu____1618) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____1667 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____1667 with
                                     | (u,uu____1682,g_u) ->
                                         let uu____1690 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____1690,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____1600 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1722 =
                             let uu____1729 =
                               let uu____1735 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____1735.FStar_Syntax_Syntax.effect_args in
                             match uu____1729 with
                             | pre::post::uu____1744 ->
                                 ((fst pre), (fst post))
                             | uu____1774 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____1722 with
                            | (pre,post) ->
                                let uu____1797 =
                                  let uu____1799 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____1799 goal.goal_ty in
                                (match uu____1797 with
                                 | None  ->
                                     let uu____1801 =
                                       let uu____1802 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____1802 in
                                     let uu____1803 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____1801 uu____1803
                                 | Some g ->
                                     let g1 =
                                       let uu____1806 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1806
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1840  ->
                                               match uu____1840 with
                                               | (uu____1847,uu____1848,uu____1849,tm2,uu____1851,uu____1852)
                                                   ->
                                                   let uu____1853 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1853 with
                                                    | (hd1,uu____1864) ->
                                                        let uu____1879 =
                                                          let uu____1880 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1880.FStar_Syntax_Syntax.n in
                                                        (match uu____1879
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1883 ->
                                                             true
                                                         | uu____1892 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____1894  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____1904 =
                                                 let uu____1908 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____1908 in
                                               FStar_List.map
                                                 FStar_Pervasives.fst
                                                 uu____1904 in
                                             FStar_List.existsML
                                               (fun u  ->
                                                  FStar_Syntax_Unionfind.equiv
                                                    u uv) free_uvars in
                                           let appears uv goals =
                                             FStar_List.existsML
                                               (fun g'  ->
                                                  is_free_uvar uv g'.goal_ty)
                                               goals in
                                           let checkone t1 goals =
                                             let uu____1936 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____1936 with
                                             | (hd1,uu____1947) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____1963) ->
                                                      appears uv goals
                                                  | uu____1976 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____1993  ->
                                                     match uu____1993 with
                                                     | (_msg,_env,_uvar,term,typ,uu____2005)
                                                         ->
                                                         let uu____2006 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____2007 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____2006;
                                                           goal_ty =
                                                             uu____2007
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____2039 = f x xs1 in
                                                 if uu____2039
                                                 then
                                                   let uu____2041 =
                                                     filter' f xs1 in
                                                   x :: uu____2041
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g2  ->
                                                  fun goals  ->
                                                    let uu____2049 =
                                                      checkone g2.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____2049) sub_goals in
                                           let uu____2050 =
                                             add_irrelevant_goal goal.context
                                               pre in
                                           bind uu____2050
                                             (fun uu____2052  ->
                                                let uu____2053 =
                                                  trytac trivial in
                                                bind uu____2053
                                                  (fun uu____2057  ->
                                                     let uu____2059 =
                                                       add_implicits
                                                         g1.FStar_TypeChecker_Env.implicits in
                                                     bind uu____2059
                                                       (fun uu____2061  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2069 =
           FStar_All.pipe_left mlog
             (fun uu____2074  ->
                let uu____2075 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2076 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2075
                  uu____2076) in
         bind uu____2069
           (fun uu____2077  ->
              let uu____2078 =
                let uu____2080 =
                  let uu____2081 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2081 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2080 in
              match uu____2078 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2088::(x,uu____2090)::(e,uu____2092)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2126 =
                    let uu____2127 = FStar_Syntax_Subst.compress x in
                    uu____2127.FStar_Syntax_Syntax.n in
                  (match uu____2126 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___97_2133 = goal in
                         let uu____2134 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2137 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___97_2133.context);
                           witness = uu____2134;
                           goal_ty = uu____2137
                         } in
                       replace_cur goal1
                   | uu____2140 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2141 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2145 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2145 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2160 = FStar_Util.set_mem x fns_ty in
           if uu____2160
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2163 =
                FStar_TypeChecker_Util.new_implicit_var "clear"
                  (goal.goal_ty).FStar_Syntax_Syntax.pos env' goal.goal_ty in
              match uu____2163 with
              | (u,uu____2172,g) ->
                  let uu____2180 =
                    let uu____2181 =
                      FStar_TypeChecker_Rel.teq_nosmt goal.context
                        goal.witness u in
                    Prims.op_Negation uu____2181 in
                  if uu____2180
                  then fail "clear: unification failed"
                  else
                    (let new_goal =
                       let uu___98_2185 = goal in
                       let uu____2186 = bnorm env' u in
                       {
                         context = env';
                         witness = uu____2186;
                         goal_ty = (uu___98_2185.goal_ty)
                       } in
                     let g1 =
                       let uu____2188 =
                         FStar_TypeChecker_Rel.solve_deferred_constraints
                           goal.context g in
                       FStar_All.pipe_right uu____2188
                         FStar_TypeChecker_Rel.resolve_implicits in
                     bind dismiss
                       (fun uu____2189  ->
                          let uu____2190 =
                            add_implicits g1.FStar_TypeChecker_Env.implicits in
                          bind uu____2190
                            (fun uu____2192  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2200 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2200 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2215 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2215 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2229 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2229 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___99_2247 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2255 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2255 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2267 = FStar_Syntax_Print.bv_to_string x in
               let uu____2268 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2267 uu____2268
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2282 = revert_all_hd xs1 in
        bind uu____2282 (fun uu____2284  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___100_2295 = g in
           {
             context = ctx';
             witness = (uu___100_2295.witness);
             goal_ty = (uu___100_2295.goal_ty)
           } in
         bind dismiss (fun uu____2296  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___101_2307 = g in
           {
             context = ctx';
             witness = (uu___101_2307.witness);
             goal_ty = (uu___101_2307.goal_ty)
           } in
         bind dismiss (fun uu____2308  -> add_goals [g']))
let rec bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2332 = FStar_Syntax_Subst.compress t in
          uu____2332.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2355 =
                let uu____2365 = ff hd1 in
                let uu____2366 =
                  FStar_List.map
                    (fun uu____2374  ->
                       match uu____2374 with
                       | (a,q) -> let uu____2381 = ff a in (uu____2381, q))
                    args in
                (uu____2365, uu____2366) in
              FStar_Syntax_Syntax.Tm_app uu____2355
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2400 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2400 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2406 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2406 t' in
                   let uu____2407 =
                     let uu____2417 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2417, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2407)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2431 -> tn in
        f env
          (let uu___102_2432 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___102_2432.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos =
               (uu___102_2432.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___102_2432.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2470 = f x in
      bind uu____2470
        (fun y  ->
           let uu____2474 = mapM f xs in
           bind uu____2474 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2509 = FStar_Syntax_Subst.compress t in
          uu____2509.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2535 = ff hd1 in
              bind uu____2535
                (fun hd2  ->
                   let fa uu____2546 =
                     match uu____2546 with
                     | (a,q) ->
                         let uu____2554 = ff a in
                         bind uu____2554 (fun a1  -> ret (a1, q)) in
                   let uu____2561 = mapM fa args in
                   bind uu____2561
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2595 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2595 with
               | (bs1,t') ->
                   let uu____2601 =
                     let uu____2603 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2603 t' in
                   bind uu____2601
                     (fun t''  ->
                        let uu____2605 =
                          let uu____2606 =
                            let uu____2616 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2616, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2606 in
                        ret uu____2605))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2630 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___103_2632 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___103_2632.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___103_2632.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___103_2632.FStar_Syntax_Syntax.vars)
                }))
let pointwise_rec:
  proofstate ->
    Prims.unit tac ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ps  ->
    fun tau  ->
      fun env  ->
        fun t  ->
          let uu____2657 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2657 with
          | (t1,lcomp,g) ->
              let uu____2665 =
                (let uu____2666 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2666) ||
                  (let uu____2667 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2667) in
              if uu____2665
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2673 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env typ in
                 match uu____2673 with
                 | (ut,uvs,guard) ->
                     (log ps
                        (fun uu____2691  ->
                           let uu____2692 =
                             FStar_Syntax_Print.term_to_string t1 in
                           let uu____2693 =
                             FStar_Syntax_Print.term_to_string ut in
                           FStar_Util.print2
                             "Pointwise_rec: making equality %s = %s\n"
                             uu____2692 uu____2693);
                      (let uu____2694 =
                         let uu____2696 =
                           let uu____2697 =
                             FStar_TypeChecker_TcTerm.universe_of env typ in
                           FStar_Syntax_Util.mk_eq2 uu____2697 typ t1 ut in
                         add_irrelevant_goal env uu____2696 in
                       bind uu____2694
                         (fun uu____2698  ->
                            let uu____2699 =
                              bind tau
                                (fun uu____2701  ->
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env guard;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.WHNF]
                                        env ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2699))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2713 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2713 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2734  ->
                   let uu____2735 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2735);
              bind dismiss_all
                (fun uu____2736  ->
                   let uu____2737 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2737
                     (fun gt'  ->
                        log ps
                          (fun uu____2741  ->
                             let uu____2742 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2742);
                        (let uu____2743 = push_goals gs in
                         bind uu____2743
                           (fun uu____2745  ->
                              add_goals
                                [(let uu___104_2746 = g in
                                  {
                                    context = (uu___104_2746.context);
                                    witness = (uu___104_2746.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2749 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2749 with
       | Some t ->
           let uu____2759 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2759 with
            | (hd1,args) ->
                let uu____2780 =
                  let uu____2788 =
                    let uu____2789 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2789.FStar_Syntax_Syntax.n in
                  (uu____2788, args) in
                (match uu____2780 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2799::(l,uu____2801)::(r,uu____2803)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.eq2_lid
                     ->
                     let l1 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.Delta_constant;
                         FStar_TypeChecker_Normalize.UnfoldTac] g.context l in
                     let r1 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.Delta_constant;
                         FStar_TypeChecker_Normalize.UnfoldTac] g.context r in
                     let uu____2839 =
                       let uu____2840 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l1 r1 in
                       Prims.op_Negation uu____2840 in
                     if uu____2839
                     then
                       let uu____2842 = FStar_Syntax_Print.term_to_string l1 in
                       let uu____2843 = FStar_Syntax_Print.term_to_string r1 in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____2842 uu____2843
                     else
                       (let t_unit1 = FStar_TypeChecker_Common.t_unit in
                        solve g t_unit1; dismiss)
                 | (hd2,uu____2850) ->
                     let uu____2861 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____2861))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___105_2871 = ps in
              {
                main_context = (uu___105_2871.main_context);
                main_goal = (uu___105_2871.main_goal);
                all_implicits = (uu___105_2871.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___105_2871.smt_goals)
              })
       | uu____2872 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___106_2880 = ps in
              {
                main_context = (uu___106_2880.main_context);
                main_goal = (uu___106_2880.main_goal);
                all_implicits = (uu___106_2880.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___106_2880.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2884 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2899 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2899 with
         | (t1,typ,guard) ->
             let uu____2909 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2909 with
              | (hd1,args) ->
                  let uu____2938 =
                    let uu____2946 =
                      let uu____2947 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2947.FStar_Syntax_Syntax.n in
                    (uu____2946, args) in
                  (match uu____2938 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2960)::(q,uu____2962)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___107_2991 = g in
                         let uu____2992 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2992;
                           witness = (uu___107_2991.witness);
                           goal_ty = (uu___107_2991.goal_ty)
                         } in
                       let g2 =
                         let uu___108_2994 = g in
                         let uu____2995 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2995;
                           witness = (uu___108_2994.witness);
                           goal_ty = (uu___108_2994.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____2998  ->
                            let uu____2999 = add_goals [g1; g2] in
                            bind uu____2999
                              (fun uu____3003  ->
                                 let uu____3004 =
                                   let uu____3007 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____3008 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____3007, uu____3008) in
                                 ret uu____3004))
                   | uu____3011 ->
                       let uu____3019 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____3019)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____3026 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____3031 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____3036 -> false
let order_binder:
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder -> order =
  fun x  ->
    fun y  ->
      let n1 = FStar_Syntax_Syntax.order_bv (fst x) (fst y) in
      if n1 < (Prims.parse_int "0")
      then Lt
      else if n1 = (Prims.parse_int "0") then Eq else Gt
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> proofstate
  =
  fun env  ->
    fun typ  ->
      let uu____3060 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____3060 with
      | (u,uu____3068,g_u) ->
          let g = { context = env; witness = u; goal_ty = typ } in
          {
            main_context = env;
            main_goal = g;
            all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
            goals = [g];
            smt_goals = []
          }
let cur_env: env tac =
  bind get
    (fun ps  ->
       let uu____3079 =
         let uu____3080 = FStar_List.hd ps.goals in uu____3080.context in
       FStar_All.pipe_left ret uu____3079)
let cur_goal': FStar_Syntax_Syntax.typ tac =
  bind get
    (fun ps  ->
       let uu____3084 =
         let uu____3085 = FStar_List.hd ps.goals in uu____3085.goal_ty in
       FStar_All.pipe_left ret uu____3084)
let cur_witness: FStar_Syntax_Syntax.term tac =
  bind get
    (fun ps  ->
       let uu____3089 =
         let uu____3090 = FStar_List.hd ps.goals in uu____3090.witness in
       FStar_All.pipe_left ret uu____3089)