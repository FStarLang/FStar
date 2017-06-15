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
         let uu___78_655 = p in
         let uu____656 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_655.main_context);
           main_goal = (uu___78_655.main_goal);
           all_implicits = (uu___78_655.all_implicits);
           goals = uu____656;
           smt_goals = (uu___78_655.smt_goals)
         } in
       set uu____654)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_660 = p in
          {
            main_context = (uu___79_660.main_context);
            main_goal = (uu___79_660.main_goal);
            all_implicits = (uu___79_660.all_implicits);
            goals = [];
            smt_goals = (uu___79_660.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_670 = p in
            {
              main_context = (uu___80_670.main_context);
              main_goal = (uu___80_670.main_goal);
              all_implicits = (uu___80_670.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_670.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_680 = p in
            {
              main_context = (uu___81_680.main_context);
              main_goal = (uu___81_680.main_goal);
              all_implicits = (uu___81_680.all_implicits);
              goals = (uu___81_680.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_690 = p in
            {
              main_context = (uu___82_690.main_context);
              main_goal = (uu___82_690.main_goal);
              all_implicits = (uu___82_690.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___82_690.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_700 = p in
            {
              main_context = (uu___83_700.main_context);
              main_goal = (uu___83_700.main_goal);
              all_implicits = (uu___83_700.all_implicits);
              goals = (uu___83_700.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____707  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_715 = p in
            {
              main_context = (uu___84_715.main_context);
              main_goal = (uu___84_715.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_715.goals);
              smt_goals = (uu___84_715.smt_goals)
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
                  let uu___85_907 = p in
                  {
                    main_context = (uu___85_907.main_context);
                    main_goal = (uu___85_907.main_goal);
                    all_implicits = (uu___85_907.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___86_909 = p in
                  {
                    main_context = (uu___86_909.main_context);
                    main_goal = (uu___86_909.main_goal);
                    all_implicits = (uu___86_909.all_implicits);
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
                                                let uu___87_933 = p in
                                                {
                                                  main_context =
                                                    (uu___87_933.main_context);
                                                  main_goal =
                                                    (uu___87_933.main_goal);
                                                  all_implicits =
                                                    (uu___87_933.all_implicits);
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
                           let uu____1120 =
                             FStar_TypeChecker_Rel.solve_deferred_constraints
                               goal.context g in
                           FStar_All.pipe_right uu____1120
                             FStar_TypeChecker_Rel.resolve_implicits in
                         let uu____1121 =
                           add_implicits g1.FStar_TypeChecker_Env.implicits in
                         bind uu____1121
                           (fun uu____1125  ->
                              let uu____1126 =
                                let uu____1128 =
                                  let uu___90_1129 = goal in
                                  let uu____1130 = bnorm env' u in
                                  let uu____1131 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1130;
                                    goal_ty = uu____1131
                                  } in
                                replace_cur uu____1128 in
                              bind uu____1126 (fun uu____1134  -> ret b1))
                       else fail "intro: unification failed"))
       | None  ->
           let uu____1142 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1142)
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
           let uu____1162 =
             let uu____1164 = FStar_List.map tr s in
             FStar_List.flatten uu____1164 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1162 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___91_1170 = goal in
            { context = (uu___91_1170.context); witness = w; goal_ty = t }))
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
       let uu____1184 = istrivial goal.context goal.goal_ty in
       if uu____1184
       then (solve goal FStar_Syntax_Const.exp_unit; dismiss)
       else
         (let uu____1188 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1188))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1196 =
           try
             let uu____1210 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1210
           with
           | e ->
               let uu____1223 = FStar_Syntax_Print.term_to_string t in
               let uu____1224 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1223
                 uu____1224 in
         bind uu____1196
           (fun uu____1231  ->
              match uu____1231 with
              | (t1,typ,guard) ->
                  let uu____1239 =
                    let uu____1240 =
                      let uu____1241 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1241 in
                    Prims.op_Negation uu____1240 in
                  if uu____1239
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1244 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1244
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1248 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1249 =
                          let uu____1250 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1250 in
                        let uu____1251 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1248 uu____1249 uu____1251))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1259 =
           try
             let uu____1273 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1273
           with
           | e ->
               let uu____1286 = FStar_Syntax_Print.term_to_string t in
               let uu____1287 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1286
                 uu____1287 in
         bind uu____1259
           (fun uu____1294  ->
              match uu____1294 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1307 =
                       let uu____1308 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1308 in
                     if uu____1307
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1311 =
                          let uu____1318 =
                            let uu____1324 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1324.FStar_Syntax_Syntax.effect_args in
                          match uu____1318 with
                          | pre::post::uu____1333 -> ((fst pre), (fst post))
                          | uu____1363 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1311 with
                        | (pre,post) ->
                            let uu____1386 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1386
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1389  ->
                                    add_irrelevant_goal goal.context pre))
                            else
                              (let uu____1391 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1392 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1393 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1391 uu____1392 uu____1393)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1404 =
          let uu____1408 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1408 in
        FStar_List.map FStar_Pervasives.fst uu____1404 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1435 = let uu____1438 = exact tm in trytac uu____1438 in
           bind uu____1435
             (fun r  ->
                match r with
                | Some r1 -> ret ()
                | None  ->
                    let uu____1445 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1445 with
                     | (tm1,typ,guard) ->
                         let uu____1453 =
                           let uu____1454 =
                             let uu____1455 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1455 in
                           Prims.op_Negation uu____1454 in
                         if uu____1453
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1458 = FStar_Syntax_Util.arrow_one typ in
                            match uu____1458 with
                            | None  ->
                                let uu____1465 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1465
                            | Some ((bv,aq),c) ->
                                let uu____1475 =
                                  let uu____1476 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____1476 in
                                if uu____1475
                                then fail "apply: not total"
                                else
                                  (let uu____1479 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   match uu____1479 with
                                   | (u,uu____1488,g_u) ->
                                       let tm' =
                                         FStar_Syntax_Syntax.mk_Tm_app tm1
                                           [(u, aq)] None
                                           (goal.context).FStar_TypeChecker_Env.range in
                                       let uu____1505 = __apply uopt tm' in
                                       bind uu____1505
                                         (fun uu____1507  ->
                                            let g_u1 =
                                              let uu____1509 =
                                                FStar_TypeChecker_Rel.solve_deferred_constraints
                                                  goal.context g_u in
                                              FStar_All.pipe_right uu____1509
                                                FStar_TypeChecker_Rel.resolve_implicits in
                                            let uu____1510 =
                                              let uu____1511 =
                                                let uu____1514 =
                                                  let uu____1515 =
                                                    FStar_Syntax_Util.head_and_args
                                                      u in
                                                  fst uu____1515 in
                                                FStar_Syntax_Subst.compress
                                                  uu____1514 in
                                              uu____1511.FStar_Syntax_Syntax.n in
                                            match uu____1510 with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                (uvar,uu____1534) ->
                                                let uu____1547 =
                                                  add_implicits
                                                    g_u1.FStar_TypeChecker_Env.implicits in
                                                bind uu____1547
                                                  (fun uu____1549  ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1551 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____1551
                                                          then ret ()
                                                          else
                                                            (let uu____1554 =
                                                               let uu____1556
                                                                 =
                                                                 let uu____1557
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____1558
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1557;
                                                                   goal_ty =
                                                                    uu____1558
                                                                 } in
                                                               [uu____1556] in
                                                             add_goals
                                                               uu____1554)))
                                            | uu____1559 -> ret ()))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1566 = __apply true tm in focus_cur_goal uu____1566
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1575 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1575 with
         | (tm1,t,guard) ->
             let uu____1583 =
               let uu____1584 =
                 let uu____1585 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1585 in
               Prims.op_Negation uu____1584 in
             if uu____1583
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1588 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____1588 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____1605 =
                         FStar_List.fold_left
                           (fun uu____1622  ->
                              fun uu____1623  ->
                                match (uu____1622, uu____1623) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____1672 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____1672 with
                                     | (u,uu____1687,g_u) ->
                                         let uu____1695 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____1695,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____1605 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1727 =
                             let uu____1734 =
                               let uu____1740 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____1740.FStar_Syntax_Syntax.effect_args in
                             match uu____1734 with
                             | pre::post::uu____1749 ->
                                 ((fst pre), (fst post))
                             | uu____1779 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____1727 with
                            | (pre,post) ->
                                let uu____1802 =
                                  let uu____1804 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____1804 goal.goal_ty in
                                (match uu____1802 with
                                 | None  ->
                                     let uu____1806 =
                                       let uu____1807 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____1807 in
                                     let uu____1808 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____1806 uu____1808
                                 | Some g ->
                                     let g1 =
                                       let uu____1811 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1811
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1845  ->
                                               match uu____1845 with
                                               | (uu____1852,uu____1853,uu____1854,tm2,uu____1856,uu____1857)
                                                   ->
                                                   let uu____1858 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1858 with
                                                    | (hd1,uu____1869) ->
                                                        let uu____1884 =
                                                          let uu____1885 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1885.FStar_Syntax_Syntax.n in
                                                        (match uu____1884
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1888 ->
                                                             true
                                                         | uu____1897 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____1899  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____1909 =
                                                 let uu____1913 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____1913 in
                                               FStar_List.map
                                                 FStar_Pervasives.fst
                                                 uu____1909 in
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
                                             let uu____1941 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____1941 with
                                             | (hd1,uu____1952) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____1968) ->
                                                      appears uv goals
                                                  | uu____1981 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____1998  ->
                                                     match uu____1998 with
                                                     | (_msg,_env,_uvar,term,typ,uu____2010)
                                                         ->
                                                         let uu____2011 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____2012 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____2011;
                                                           goal_ty =
                                                             uu____2012
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____2044 = f x xs1 in
                                                 if uu____2044
                                                 then
                                                   let uu____2046 =
                                                     filter' f xs1 in
                                                   x :: uu____2046
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g2  ->
                                                  fun goals  ->
                                                    let uu____2054 =
                                                      checkone g2.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____2054) sub_goals in
                                           let uu____2055 =
                                             add_irrelevant_goal goal.context
                                               pre in
                                           bind uu____2055
                                             (fun uu____2057  ->
                                                let uu____2058 =
                                                  trytac trivial in
                                                bind uu____2058
                                                  (fun uu____2062  ->
                                                     let uu____2064 =
                                                       add_implicits
                                                         g1.FStar_TypeChecker_Env.implicits in
                                                     bind uu____2064
                                                       (fun uu____2066  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2074 =
           FStar_All.pipe_left mlog
             (fun uu____2079  ->
                let uu____2080 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2081 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2080
                  uu____2081) in
         bind uu____2074
           (fun uu____2082  ->
              let uu____2083 =
                let uu____2085 =
                  let uu____2086 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2086 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2085 in
              match uu____2083 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2093::(x,uu____2095)::(e,uu____2097)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2131 =
                    let uu____2132 = FStar_Syntax_Subst.compress x in
                    uu____2132.FStar_Syntax_Syntax.n in
                  (match uu____2131 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___96_2138 = goal in
                         let uu____2139 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2142 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___96_2138.context);
                           witness = uu____2139;
                           goal_ty = uu____2142
                         } in
                       replace_cur goal1
                   | uu____2145 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2146 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2150 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2150 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2165 = FStar_Util.set_mem x fns_ty in
           if uu____2165
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2168 =
                FStar_TypeChecker_Util.new_implicit_var "clear"
                  (goal.goal_ty).FStar_Syntax_Syntax.pos env' goal.goal_ty in
              match uu____2168 with
              | (u,uu____2177,g) ->
                  let uu____2185 =
                    let uu____2186 =
                      FStar_TypeChecker_Rel.teq_nosmt goal.context
                        goal.witness u in
                    Prims.op_Negation uu____2186 in
                  if uu____2185
                  then fail "clear: unification failed"
                  else
                    (let new_goal =
                       let uu___97_2190 = goal in
                       let uu____2191 = bnorm env' u in
                       {
                         context = env';
                         witness = uu____2191;
                         goal_ty = (uu___97_2190.goal_ty)
                       } in
                     let g1 =
                       let uu____2193 =
                         FStar_TypeChecker_Rel.solve_deferred_constraints
                           goal.context g in
                       FStar_All.pipe_right uu____2193
                         FStar_TypeChecker_Rel.resolve_implicits in
                     bind dismiss
                       (fun uu____2194  ->
                          let uu____2195 =
                            add_implicits g1.FStar_TypeChecker_Env.implicits in
                          bind uu____2195
                            (fun uu____2197  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2205 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2205 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2220 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2220 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2234 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2234 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___98_2257 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2265 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2265 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2277 = FStar_Syntax_Print.bv_to_string x in
               let uu____2278 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2277 uu____2278
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2292 = revert_all_hd xs1 in
        bind uu____2292 (fun uu____2294  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___99_2305 = g in
           {
             context = ctx';
             witness = (uu___99_2305.witness);
             goal_ty = (uu___99_2305.goal_ty)
           } in
         bind dismiss (fun uu____2306  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___100_2317 = g in
           {
             context = ctx';
             witness = (uu___100_2317.witness);
             goal_ty = (uu___100_2317.goal_ty)
           } in
         bind dismiss (fun uu____2318  -> add_goals [g']))
let rec bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2342 = FStar_Syntax_Subst.compress t in
          uu____2342.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2365 =
                let uu____2375 = ff hd1 in
                let uu____2376 =
                  FStar_List.map
                    (fun uu____2384  ->
                       match uu____2384 with
                       | (a,q) -> let uu____2391 = ff a in (uu____2391, q))
                    args in
                (uu____2375, uu____2376) in
              FStar_Syntax_Syntax.Tm_app uu____2365
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2420 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2420 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2426 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2426 t' in
                   let uu____2427 =
                     let uu____2442 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2442, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2427)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2461 -> tn in
        f env
          (let uu___101_2462 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___101_2462.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos =
               (uu___101_2462.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___101_2462.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2500 = f x in
      bind uu____2500
        (fun y  ->
           let uu____2504 = mapM f xs in
           bind uu____2504 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2539 = FStar_Syntax_Subst.compress t in
          uu____2539.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2565 = ff hd1 in
              bind uu____2565
                (fun hd2  ->
                   let fa uu____2576 =
                     match uu____2576 with
                     | (a,q) ->
                         let uu____2584 = ff a in
                         bind uu____2584 (fun a1  -> ret (a1, q)) in
                   let uu____2591 = mapM fa args in
                   bind uu____2591
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2635 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2635 with
               | (bs1,t') ->
                   let uu____2641 =
                     let uu____2643 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2643 t' in
                   bind uu____2641
                     (fun t''  ->
                        let uu____2645 =
                          let uu____2646 =
                            let uu____2661 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2661, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2646 in
                        ret uu____2645))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2680 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___102_2682 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___102_2682.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___102_2682.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___102_2682.FStar_Syntax_Syntax.vars)
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
          let uu____2707 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2707 with
          | (t1,lcomp,g) ->
              let uu____2715 =
                (let uu____2716 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2716) ||
                  (let uu____2717 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2717) in
              if uu____2715
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2723 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env typ in
                 match uu____2723 with
                 | (ut,uvs,guard) ->
                     (log ps
                        (fun uu____2741  ->
                           let uu____2742 =
                             FStar_Syntax_Print.term_to_string t1 in
                           let uu____2743 =
                             FStar_Syntax_Print.term_to_string ut in
                           FStar_Util.print2
                             "Pointwise_rec: making equality %s = %s\n"
                             uu____2742 uu____2743);
                      (let uu____2744 =
                         let uu____2746 =
                           let uu____2747 =
                             FStar_TypeChecker_TcTerm.universe_of env typ in
                           FStar_Syntax_Util.mk_eq2 uu____2747 typ t1 ut in
                         add_irrelevant_goal env uu____2746 in
                       bind uu____2744
                         (fun uu____2748  ->
                            let uu____2749 =
                              bind tau
                                (fun uu____2751  ->
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env guard;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.WHNF]
                                        env ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2749))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2763 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2763 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2784  ->
                   let uu____2785 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2785);
              bind dismiss_all
                (fun uu____2786  ->
                   let uu____2787 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2787
                     (fun gt'  ->
                        log ps
                          (fun uu____2791  ->
                             let uu____2792 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2792);
                        (let uu____2793 = push_goals gs in
                         bind uu____2793
                           (fun uu____2795  ->
                              add_goals
                                [(let uu___103_2796 = g in
                                  {
                                    context = (uu___103_2796.context);
                                    witness = (uu___103_2796.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2799 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2799 with
       | Some t ->
           let uu____2809 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2809 with
            | (hd1,args) ->
                let uu____2830 =
                  let uu____2838 =
                    let uu____2839 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2839.FStar_Syntax_Syntax.n in
                  (uu____2838, args) in
                (match uu____2830 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2849::(l,uu____2851)::(r,uu____2853)::[]) when
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
                     let uu____2889 =
                       let uu____2890 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l1 r1 in
                       Prims.op_Negation uu____2890 in
                     if uu____2889
                     then
                       let uu____2892 = FStar_Syntax_Print.term_to_string l1 in
                       let uu____2893 = FStar_Syntax_Print.term_to_string r1 in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____2892 uu____2893
                     else
                       (let t_unit1 = FStar_TypeChecker_Common.t_unit in
                        solve g t_unit1; dismiss)
                 | (hd2,uu____2900) ->
                     let uu____2911 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____2911))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___104_2921 = ps in
              {
                main_context = (uu___104_2921.main_context);
                main_goal = (uu___104_2921.main_goal);
                all_implicits = (uu___104_2921.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___104_2921.smt_goals)
              })
       | uu____2922 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___105_2930 = ps in
              {
                main_context = (uu___105_2930.main_context);
                main_goal = (uu___105_2930.main_goal);
                all_implicits = (uu___105_2930.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___105_2930.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2934 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2949 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2949 with
         | (t1,typ,guard) ->
             let uu____2959 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2959 with
              | (hd1,args) ->
                  let uu____2988 =
                    let uu____2996 =
                      let uu____2997 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2997.FStar_Syntax_Syntax.n in
                    (uu____2996, args) in
                  (match uu____2988 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____3010)::(q,uu____3012)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___106_3041 = g in
                         let uu____3042 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____3042;
                           witness = (uu___106_3041.witness);
                           goal_ty = (uu___106_3041.goal_ty)
                         } in
                       let g2 =
                         let uu___107_3044 = g in
                         let uu____3045 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____3045;
                           witness = (uu___107_3044.witness);
                           goal_ty = (uu___107_3044.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____3048  ->
                            let uu____3049 = add_goals [g1; g2] in
                            bind uu____3049
                              (fun uu____3053  ->
                                 let uu____3054 =
                                   let uu____3057 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____3058 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____3057, uu____3058) in
                                 ret uu____3054))
                   | uu____3061 ->
                       let uu____3069 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____3069)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____3076 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____3081 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____3086 -> false
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
      let uu____3110 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____3110 with
      | (u,uu____3118,g_u) ->
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
       let uu____3129 =
         let uu____3130 = FStar_List.hd ps.goals in uu____3130.context in
       FStar_All.pipe_left ret uu____3129)
let cur_goal': FStar_Syntax_Syntax.typ tac =
  bind get
    (fun ps  ->
       let uu____3134 =
         let uu____3135 = FStar_List.hd ps.goals in uu____3135.goal_ty in
       FStar_All.pipe_left ret uu____3134)
let cur_witness: FStar_Syntax_Syntax.term tac =
  bind get
    (fun ps  ->
       let uu____3139 =
         let uu____3140 = FStar_List.hd ps.goals in uu____3140.witness in
       FStar_All.pipe_left ret uu____3139)