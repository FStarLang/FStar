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
  match projectee with | Success _0 -> true | uu____106 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success _0 -> _0
let uu___is_Failed projectee =
  match projectee with | Failed _0 -> true | uu____137 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed _0 -> _0
exception TacFailure of Prims.string
let uu___is_TacFailure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | TacFailure uu____162 -> true | uu____163 -> false
let __proj__TacFailure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | TacFailure uu____170 -> uu____170
type 'a tac = {
  tac_f: proofstate -> 'a result;}
let mk_tac f = { tac_f = f }
let run t p = t.tac_f p
let ret x = mk_tac (fun p  -> Success (x, p))
let bind t1 t2 =
  mk_tac
    (fun p  ->
       let uu____265 = run t1 p in
       match uu____265 with
       | Success (a,q) -> let uu____270 = t2 a in run uu____270 q
       | Failed (msg,q) -> Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____279 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____279
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____280 = FStar_Syntax_Print.term_to_string g.witness in
    let uu____281 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____280 uu____281
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____291 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____291
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____301 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____301
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____314 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____314
let comp_to_typ:
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____319) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____327) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: goal -> Prims.bool =
  fun g  ->
    let uu____338 = FStar_Syntax_Util.un_squash g.goal_ty in
    match uu____338 with | Some t -> true | uu____347 -> false
let dump_goal ps goal =
  let uu____364 = goal_to_string goal in tacprint uu____364
let dump_cur: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____372 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____375 = FStar_List.hd ps.goals in dump_goal ps uu____375))
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____385 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____385);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____391 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____391);
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
      let uu____428 = FStar_ST.read tac_verb_dbg in
      match uu____428 with
      | None  ->
          ((let uu____434 =
              let uu____436 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              Some uu____436 in
            FStar_ST.write tac_verb_dbg uu____434);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____462 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____462
        then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
        else ());
       Failed (msg, ps))
let fail1 msg x = let uu____477 = FStar_Util.format1 msg x in fail uu____477
let fail2 msg x y =
  let uu____496 = FStar_Util.format2 msg x y in fail uu____496
let fail3 msg x y z =
  let uu____520 = FStar_Util.format3 msg x y z in fail uu____520
let trytac t =
  mk_tac
    (fun ps  ->
       let tx = FStar_Syntax_Unionfind.new_transaction () in
       let uu____535 = run t ps in
       match uu____535 with
       | Success (a,q) ->
           (FStar_Syntax_Unionfind.commit tx; Success ((Some a), q))
       | Failed (uu____544,uu____545) ->
           (FStar_Syntax_Unionfind.rollback tx; Success (None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____554  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____561 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____561
      then ()
      else
        (let uu____563 =
           let uu____564 =
             let uu____565 = FStar_Syntax_Print.term_to_string solution in
             let uu____566 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____567 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____565
               uu____566 uu____567 in
           TacFailure uu____564 in
         raise uu____563)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____570 =
         let uu___79_571 = p in
         let uu____572 = FStar_List.tl p.goals in
         {
           main_context = (uu___79_571.main_context);
           main_goal = (uu___79_571.main_goal);
           all_implicits = (uu___79_571.all_implicits);
           goals = uu____572;
           smt_goals = (uu___79_571.smt_goals)
         } in
       set uu____570)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___80_576 = p in
          {
            main_context = (uu___80_576.main_context);
            main_goal = (uu___80_576.main_goal);
            all_implicits = (uu___80_576.all_implicits);
            goals = [];
            smt_goals = (uu___80_576.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_585 = p in
            {
              main_context = (uu___81_585.main_context);
              main_goal = (uu___81_585.main_goal);
              all_implicits = (uu___81_585.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___81_585.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_594 = p in
            {
              main_context = (uu___82_594.main_context);
              main_goal = (uu___82_594.main_goal);
              all_implicits = (uu___82_594.all_implicits);
              goals = (uu___82_594.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_603 = p in
            {
              main_context = (uu___83_603.main_context);
              main_goal = (uu___83_603.main_goal);
              all_implicits = (uu___83_603.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___83_603.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_612 = p in
            {
              main_context = (uu___84_612.main_context);
              main_goal = (uu___84_612.main_goal);
              all_implicits = (uu___84_612.all_implicits);
              goals = (uu___84_612.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____618  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___85_625 = p in
            {
              main_context = (uu___85_625.main_context);
              main_goal = (uu___85_625.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___85_625.goals);
              smt_goals = (uu___85_625.smt_goals)
            }))
let add_irrelevant_goal: env -> FStar_Syntax_Syntax.typ -> Prims.unit tac =
  fun env  ->
    fun phi  ->
      let typ = FStar_Syntax_Util.mk_squash phi in
      let uu____643 =
        FStar_TypeChecker_Util.new_implicit_var "add_irrelevant_goal"
          phi.FStar_Syntax_Syntax.pos env typ in
      match uu____643 with
      | (u,uu____652,g_u) ->
          let goal = { context = env; witness = u; goal_ty = typ } in
          let uu____661 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____661 (fun uu____663  -> add_goals [goal])
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____667 = FStar_Syntax_Util.un_squash t in
    match uu____667 with
    | Some t' ->
        let uu____676 =
          let uu____677 = FStar_Syntax_Subst.compress t' in
          uu____677.FStar_Syntax_Syntax.n in
        (match uu____676 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____681 -> false)
    | uu____682 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____689 = FStar_Syntax_Util.un_squash t in
    match uu____689 with
    | Some t' ->
        let uu____698 =
          let uu____699 = FStar_Syntax_Subst.compress t' in
          uu____699.FStar_Syntax_Syntax.n in
        (match uu____698 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____703 -> false)
    | uu____704 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____716 = is_irrelevant g in
       if uu____716
       then bind dismiss (fun uu____718  -> add_smt_goals [g])
       else
         (let uu____720 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____720))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____750 =
         try let uu____767 = FStar_List.splitAt n1 p.goals in ret uu____767
         with | uu____782 -> fail "divide: not enough goals" in
       bind uu____750
         (fun uu____793  ->
            match uu____793 with
            | (lgs,rgs) ->
                let lp =
                  let uu___86_808 = p in
                  {
                    main_context = (uu___86_808.main_context);
                    main_goal = (uu___86_808.main_goal);
                    all_implicits = (uu___86_808.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___87_810 = p in
                  {
                    main_context = (uu___87_810.main_context);
                    main_goal = (uu___87_810.main_goal);
                    all_implicits = (uu___87_810.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____811 = set lp in
                bind uu____811
                  (fun uu____815  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____822 = set rp in
                               bind uu____822
                                 (fun uu____826  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___88_834 = p in
                                                {
                                                  main_context =
                                                    (uu___88_834.main_context);
                                                  main_goal =
                                                    (uu___88_834.main_goal);
                                                  all_implicits =
                                                    (uu___88_834.all_implicits);
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
                                              let uu____835 = set p' in
                                              bind uu____835
                                                (fun uu____839  -> ret (a, b))))))))))
let focus_cur_goal f =
  let uu____852 = divide (Prims.parse_int "1") f idtac in
  bind uu____852 (fun uu____858  -> match uu____858 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____879::uu____880 ->
           let uu____882 =
             let uu____887 = map tau in
             divide (Prims.parse_int "1") tau uu____887 in
           bind uu____882
             (fun uu____895  -> match uu____895 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____918 =
        bind t1
          (fun uu____920  ->
             let uu____921 = map t2 in
             bind uu____921 (fun uu____925  -> ret ())) in
      focus_cur_goal uu____918
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____933 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____933 with
       | Some (b,c) ->
           let uu____944 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____944 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____964 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____967 =
                  let uu____968 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____968 in
                if uu____967
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____981 =
                     FStar_TypeChecker_Util.new_implicit_var "intro"
                       typ'.FStar_Syntax_Syntax.pos env' typ' in
                   match uu____981 with
                   | (u,uu____992,g) ->
                       let uu____1000 =
                         let uu____1001 = FStar_Syntax_Util.abs [b1] u None in
                         FStar_TypeChecker_Rel.teq_nosmt goal.context
                           goal.witness uu____1001 in
                       if uu____1000
                       then
                         let g1 =
                           let uu____1010 =
                             FStar_TypeChecker_Rel.solve_deferred_constraints
                               goal.context g in
                           FStar_All.pipe_right uu____1010
                             FStar_TypeChecker_Rel.resolve_implicits in
                         let uu____1011 =
                           add_implicits g1.FStar_TypeChecker_Env.implicits in
                         bind uu____1011
                           (fun uu____1015  ->
                              let uu____1016 =
                                let uu____1018 =
                                  let uu___91_1019 = goal in
                                  let uu____1020 = bnorm env' u in
                                  let uu____1021 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1020;
                                    goal_ty = uu____1021
                                  } in
                                replace_cur uu____1018 in
                              bind uu____1016 (fun uu____1024  -> ret b1))
                       else fail "intro: unification failed"))
       | None  ->
           let uu____1032 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1032)
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
           let uu____1051 =
             let uu____1053 = FStar_List.map tr s in
             FStar_List.flatten uu____1053 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1051 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___92_1059 = goal in
            { context = (uu___92_1059.context); witness = w; goal_ty = t }))
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
       let uu____1071 = istrivial goal.context goal.goal_ty in
       if uu____1071
       then (solve goal FStar_Syntax_Const.exp_unit; dismiss)
       else
         (let uu____1075 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1075))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1082 =
           try
             let uu____1096 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1096
           with
           | e ->
               let uu____1109 = FStar_Syntax_Print.term_to_string t in
               let uu____1110 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1109
                 uu____1110 in
         bind uu____1082
           (fun uu____1117  ->
              match uu____1117 with
              | (t1,typ,guard) ->
                  let uu____1125 =
                    let uu____1126 =
                      let uu____1127 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1127 in
                    Prims.op_Negation uu____1126 in
                  if uu____1125
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1130 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1130
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1134 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1135 =
                          let uu____1136 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1136 in
                        let uu____1137 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1134 uu____1135 uu____1137))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1144 =
           try
             let uu____1158 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1158
           with
           | e ->
               let uu____1171 = FStar_Syntax_Print.term_to_string t in
               let uu____1172 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1171
                 uu____1172 in
         bind uu____1144
           (fun uu____1179  ->
              match uu____1179 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1192 =
                       let uu____1193 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1193 in
                     if uu____1192
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1196 =
                          let uu____1203 =
                            let uu____1209 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1209.FStar_Syntax_Syntax.effect_args in
                          match uu____1203 with
                          | pre::post::uu____1218 -> ((fst pre), (fst post))
                          | uu____1248 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1196 with
                        | (pre,post) ->
                            let uu____1271 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1271
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1274  ->
                                    add_irrelevant_goal goal.context pre))
                            else
                              (let uu____1276 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1277 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1278 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1276 uu____1277 uu____1278)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1287 =
          let uu____1291 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1291 in
        FStar_List.map FStar_Pervasives.fst uu____1287 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1314 = let uu____1317 = exact tm in trytac uu____1317 in
           bind uu____1314
             (fun r  ->
                match r with
                | Some r1 -> ret ()
                | None  ->
                    let uu____1324 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1324 with
                     | (tm1,typ,guard) ->
                         let uu____1332 =
                           let uu____1333 =
                             let uu____1334 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1334 in
                           Prims.op_Negation uu____1333 in
                         if uu____1332
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1337 = FStar_Syntax_Util.arrow_one typ in
                            match uu____1337 with
                            | None  ->
                                let uu____1344 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1344
                            | Some ((bv,aq),c) ->
                                let uu____1354 =
                                  let uu____1355 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____1355 in
                                if uu____1354
                                then fail "apply: not total"
                                else
                                  (let uu____1358 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   match uu____1358 with
                                   | (u,uu____1367,g_u) ->
                                       let tm' =
                                         FStar_Syntax_Syntax.mk_Tm_app tm1
                                           [(u, aq)] None
                                           (goal.context).FStar_TypeChecker_Env.range in
                                       let uu____1384 = __apply uopt tm' in
                                       bind uu____1384
                                         (fun uu____1386  ->
                                            let g_u1 =
                                              let uu____1388 =
                                                FStar_TypeChecker_Rel.solve_deferred_constraints
                                                  goal.context g_u in
                                              FStar_All.pipe_right uu____1388
                                                FStar_TypeChecker_Rel.resolve_implicits in
                                            let uu____1389 =
                                              let uu____1390 =
                                                let uu____1393 =
                                                  let uu____1394 =
                                                    FStar_Syntax_Util.head_and_args
                                                      u in
                                                  fst uu____1394 in
                                                FStar_Syntax_Subst.compress
                                                  uu____1393 in
                                              uu____1390.FStar_Syntax_Syntax.n in
                                            match uu____1389 with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                (uvar,uu____1413) ->
                                                let uu____1426 =
                                                  add_implicits
                                                    g_u1.FStar_TypeChecker_Env.implicits in
                                                bind uu____1426
                                                  (fun uu____1428  ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1430 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____1430
                                                          then ret ()
                                                          else
                                                            (let uu____1433 =
                                                               let uu____1435
                                                                 =
                                                                 let uu____1436
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____1437
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1436;
                                                                   goal_ty =
                                                                    uu____1437
                                                                 } in
                                                               [uu____1435] in
                                                             add_goals
                                                               uu____1433)))
                                            | uu____1438 -> ret ()))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1444 = __apply true tm in focus_cur_goal uu____1444
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1452 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1452 with
         | (tm1,t,guard) ->
             let uu____1460 =
               let uu____1461 =
                 let uu____1462 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1462 in
               Prims.op_Negation uu____1461 in
             if uu____1460
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1465 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____1465 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____1482 =
                         FStar_List.fold_left
                           (fun uu____1499  ->
                              fun uu____1500  ->
                                match (uu____1499, uu____1500) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____1549 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____1549 with
                                     | (u,uu____1564,g_u) ->
                                         let uu____1572 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____1572,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____1482 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1604 =
                             let uu____1611 =
                               let uu____1617 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____1617.FStar_Syntax_Syntax.effect_args in
                             match uu____1611 with
                             | pre::post::uu____1626 ->
                                 ((fst pre), (fst post))
                             | uu____1656 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____1604 with
                            | (pre,post) ->
                                let uu____1679 =
                                  let uu____1681 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____1681 goal.goal_ty in
                                (match uu____1679 with
                                 | None  ->
                                     let uu____1683 =
                                       let uu____1684 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____1684 in
                                     let uu____1685 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____1683 uu____1685
                                 | Some g ->
                                     let g1 =
                                       let uu____1688 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1688
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1722  ->
                                               match uu____1722 with
                                               | (uu____1729,uu____1730,uu____1731,tm2,uu____1733,uu____1734)
                                                   ->
                                                   let uu____1735 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1735 with
                                                    | (hd1,uu____1746) ->
                                                        let uu____1761 =
                                                          let uu____1762 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1762.FStar_Syntax_Syntax.n in
                                                        (match uu____1761
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1765 ->
                                                             true
                                                         | uu____1774 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____1776  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____1786 =
                                                 let uu____1790 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____1790 in
                                               FStar_List.map
                                                 FStar_Pervasives.fst
                                                 uu____1786 in
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
                                             let uu____1818 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____1818 with
                                             | (hd1,uu____1829) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____1845) ->
                                                      appears uv goals
                                                  | uu____1858 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____1875  ->
                                                     match uu____1875 with
                                                     | (_msg,_env,_uvar,term,typ,uu____1887)
                                                         ->
                                                         let uu____1888 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____1889 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____1888;
                                                           goal_ty =
                                                             uu____1889
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____1921 = f x xs1 in
                                                 if uu____1921
                                                 then
                                                   let uu____1923 =
                                                     filter' f xs1 in
                                                   x :: uu____1923
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g2  ->
                                                  fun goals  ->
                                                    let uu____1931 =
                                                      checkone g2.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____1931) sub_goals in
                                           let uu____1932 =
                                             add_irrelevant_goal goal.context
                                               pre in
                                           bind uu____1932
                                             (fun uu____1934  ->
                                                let uu____1935 =
                                                  trytac trivial in
                                                bind uu____1935
                                                  (fun uu____1939  ->
                                                     let uu____1941 =
                                                       add_implicits
                                                         g1.FStar_TypeChecker_Env.implicits in
                                                     bind uu____1941
                                                       (fun uu____1943  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____1950 =
           FStar_All.pipe_left mlog
             (fun uu____1955  ->
                let uu____1956 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____1957 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1956
                  uu____1957) in
         bind uu____1950
           (fun uu____1958  ->
              let uu____1959 =
                let uu____1961 =
                  let uu____1962 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____1962 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1961 in
              match uu____1959 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1969::(x,uu____1971)::(e,uu____1973)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2007 =
                    let uu____2008 = FStar_Syntax_Subst.compress x in
                    uu____2008.FStar_Syntax_Syntax.n in
                  (match uu____2007 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___97_2014 = goal in
                         let uu____2015 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2018 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___97_2014.context);
                           witness = uu____2015;
                           goal_ty = uu____2018
                         } in
                       replace_cur goal1
                   | uu____2021 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2022 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2026 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2026 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2041 = FStar_Util.set_mem x fns_ty in
           if uu____2041
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2044 =
                FStar_TypeChecker_Util.new_implicit_var "clear"
                  (goal.goal_ty).FStar_Syntax_Syntax.pos env' goal.goal_ty in
              match uu____2044 with
              | (u,uu____2053,g) ->
                  let uu____2061 =
                    let uu____2062 =
                      FStar_TypeChecker_Rel.teq_nosmt goal.context
                        goal.witness u in
                    Prims.op_Negation uu____2062 in
                  if uu____2061
                  then fail "clear: unification failed"
                  else
                    (let new_goal =
                       let uu___98_2066 = goal in
                       let uu____2067 = bnorm env' u in
                       {
                         context = env';
                         witness = uu____2067;
                         goal_ty = (uu___98_2066.goal_ty)
                       } in
                     let g1 =
                       let uu____2069 =
                         FStar_TypeChecker_Rel.solve_deferred_constraints
                           goal.context g in
                       FStar_All.pipe_right uu____2069
                         FStar_TypeChecker_Rel.resolve_implicits in
                     bind dismiss
                       (fun uu____2070  ->
                          let uu____2071 =
                            add_implicits g1.FStar_TypeChecker_Env.implicits in
                          bind uu____2071
                            (fun uu____2073  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2080 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2080 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2095 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2095 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2109 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2109 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___99_2127 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2134 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2134 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2146 = FStar_Syntax_Print.bv_to_string x in
               let uu____2147 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2146 uu____2147
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2160 = revert_all_hd xs1 in
        bind uu____2160 (fun uu____2162  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___100_2172 = g in
           {
             context = ctx';
             witness = (uu___100_2172.witness);
             goal_ty = (uu___100_2172.goal_ty)
           } in
         bind dismiss (fun uu____2173  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___101_2183 = g in
           {
             context = ctx';
             witness = (uu___101_2183.witness);
             goal_ty = (uu___101_2183.goal_ty)
           } in
         bind dismiss (fun uu____2184  -> add_goals [g']))
let rec bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2205 = FStar_Syntax_Subst.compress t in
          uu____2205.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2228 =
                let uu____2238 = ff hd1 in
                let uu____2239 =
                  FStar_List.map
                    (fun uu____2247  ->
                       match uu____2247 with
                       | (a,q) -> let uu____2254 = ff a in (uu____2254, q))
                    args in
                (uu____2238, uu____2239) in
              FStar_Syntax_Syntax.Tm_app uu____2228
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2273 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2273 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2279 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2279 t' in
                   let uu____2280 =
                     let uu____2290 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2290, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2280)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2304 -> tn in
        f env
          (let uu___102_2305 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___102_2305.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos =
               (uu___102_2305.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___102_2305.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2339 = f x in
      bind uu____2339
        (fun y  ->
           let uu____2343 = mapM f xs in
           bind uu____2343 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2375 = FStar_Syntax_Subst.compress t in
          uu____2375.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2401 = ff hd1 in
              bind uu____2401
                (fun hd2  ->
                   let fa uu____2412 =
                     match uu____2412 with
                     | (a,q) ->
                         let uu____2420 = ff a in
                         bind uu____2420 (fun a1  -> ret (a1, q)) in
                   let uu____2427 = mapM fa args in
                   bind uu____2427
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2461 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2461 with
               | (bs1,t') ->
                   let uu____2467 =
                     let uu____2469 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2469 t' in
                   bind uu____2467
                     (fun t''  ->
                        let uu____2471 =
                          let uu____2472 =
                            let uu____2482 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2482, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2472 in
                        ret uu____2471))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2496 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___103_2498 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___103_2498.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___103_2498.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___103_2498.FStar_Syntax_Syntax.vars)
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
          let uu____2519 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2519 with
          | (t1,lcomp,g) ->
              let uu____2527 =
                (let uu____2528 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2528) ||
                  (let uu____2529 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2529) in
              if uu____2527
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2535 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env typ in
                 match uu____2535 with
                 | (ut,uvs,guard) ->
                     (log ps
                        (fun uu____2553  ->
                           let uu____2554 =
                             FStar_Syntax_Print.term_to_string t1 in
                           let uu____2555 =
                             FStar_Syntax_Print.term_to_string ut in
                           FStar_Util.print2
                             "Pointwise_rec: making equality %s = %s\n"
                             uu____2554 uu____2555);
                      (let uu____2556 =
                         let uu____2558 =
                           let uu____2559 =
                             FStar_TypeChecker_TcTerm.universe_of env typ in
                           FStar_Syntax_Util.mk_eq2 uu____2559 typ t1 ut in
                         add_irrelevant_goal env uu____2558 in
                       bind uu____2556
                         (fun uu____2560  ->
                            let uu____2561 =
                              bind tau
                                (fun uu____2563  ->
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env guard;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.WHNF]
                                        env ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2561))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2574 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2574 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2595  ->
                   let uu____2596 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2596);
              bind dismiss_all
                (fun uu____2597  ->
                   let uu____2598 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2598
                     (fun gt'  ->
                        log ps
                          (fun uu____2602  ->
                             let uu____2603 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2603);
                        (let uu____2604 = push_goals gs in
                         bind uu____2604
                           (fun uu____2606  ->
                              add_goals
                                [(let uu___104_2607 = g in
                                  {
                                    context = (uu___104_2607.context);
                                    witness = (uu___104_2607.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2610 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2610 with
       | Some t ->
           let uu____2620 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2620 with
            | (hd1,args) ->
                let uu____2641 =
                  let uu____2649 =
                    let uu____2650 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2650.FStar_Syntax_Syntax.n in
                  (uu____2649, args) in
                (match uu____2641 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2660::(l,uu____2662)::(r,uu____2664)::[]) when
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
                     let uu____2700 =
                       let uu____2701 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l1 r1 in
                       Prims.op_Negation uu____2701 in
                     if uu____2700
                     then
                       let uu____2703 = FStar_Syntax_Print.term_to_string l1 in
                       let uu____2704 = FStar_Syntax_Print.term_to_string r1 in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____2703 uu____2704
                     else
                       (let t_unit1 = FStar_TypeChecker_Common.t_unit in
                        solve g t_unit1; dismiss)
                 | (hd2,uu____2711) ->
                     let uu____2722 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____2722))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___105_2732 = ps in
              {
                main_context = (uu___105_2732.main_context);
                main_goal = (uu___105_2732.main_goal);
                all_implicits = (uu___105_2732.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___105_2732.smt_goals)
              })
       | uu____2733 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___106_2741 = ps in
              {
                main_context = (uu___106_2741.main_context);
                main_goal = (uu___106_2741.main_goal);
                all_implicits = (uu___106_2741.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___106_2741.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2745 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2759 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2759 with
         | (t1,typ,guard) ->
             let uu____2769 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2769 with
              | (hd1,args) ->
                  let uu____2798 =
                    let uu____2806 =
                      let uu____2807 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2807.FStar_Syntax_Syntax.n in
                    (uu____2806, args) in
                  (match uu____2798 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2820)::(q,uu____2822)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___107_2851 = g in
                         let uu____2852 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2852;
                           witness = (uu___107_2851.witness);
                           goal_ty = (uu___107_2851.goal_ty)
                         } in
                       let g2 =
                         let uu___108_2854 = g in
                         let uu____2855 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2855;
                           witness = (uu___108_2854.witness);
                           goal_ty = (uu___108_2854.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____2858  ->
                            let uu____2859 = add_goals [g1; g2] in
                            bind uu____2859
                              (fun uu____2863  ->
                                 let uu____2864 =
                                   let uu____2867 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____2868 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____2867, uu____2868) in
                                 ret uu____2864))
                   | uu____2871 ->
                       let uu____2879 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____2879)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2885 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2889 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2893 -> false
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
      let uu____2913 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____2913 with
      | (u,uu____2921,g_u) ->
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
       let uu____2932 =
         let uu____2933 = FStar_List.hd ps.goals in uu____2933.context in
       FStar_All.pipe_left ret uu____2932)
let cur_goal': FStar_Syntax_Syntax.typ tac =
  bind get
    (fun ps  ->
       let uu____2937 =
         let uu____2938 = FStar_List.hd ps.goals in uu____2938.goal_ty in
       FStar_All.pipe_left ret uu____2937)
let cur_witness: FStar_Syntax_Syntax.term tac =
  bind get
    (fun ps  ->
       let uu____2942 =
         let uu____2943 = FStar_List.hd ps.goals in uu____2943.witness in
       FStar_All.pipe_left ret uu____2942)