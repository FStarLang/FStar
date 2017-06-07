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
        if uu____462 then dump_proofstate ps "TACTING FAILING" else ());
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
         let uu___78_571 = p in
         let uu____572 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_571.main_context);
           main_goal = (uu___78_571.main_goal);
           all_implicits = (uu___78_571.all_implicits);
           goals = uu____572;
           smt_goals = (uu___78_571.smt_goals)
         } in
       set uu____570)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_576 = p in
          {
            main_context = (uu___79_576.main_context);
            main_goal = (uu___79_576.main_goal);
            all_implicits = (uu___79_576.all_implicits);
            goals = [];
            smt_goals = (uu___79_576.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_585 = p in
            {
              main_context = (uu___80_585.main_context);
              main_goal = (uu___80_585.main_goal);
              all_implicits = (uu___80_585.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_585.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_594 = p in
            {
              main_context = (uu___81_594.main_context);
              main_goal = (uu___81_594.main_goal);
              all_implicits = (uu___81_594.all_implicits);
              goals = (uu___81_594.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_603 = p in
            {
              main_context = (uu___82_603.main_context);
              main_goal = (uu___82_603.main_goal);
              all_implicits = (uu___82_603.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___82_603.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_612 = p in
            {
              main_context = (uu___83_612.main_context);
              main_goal = (uu___83_612.main_goal);
              all_implicits = (uu___83_612.all_implicits);
              goals = (uu___83_612.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____618  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_625 = p in
            {
              main_context = (uu___84_625.main_context);
              main_goal = (uu___84_625.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_625.goals);
              smt_goals = (uu___84_625.smt_goals)
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
                  let uu___85_808 = p in
                  {
                    main_context = (uu___85_808.main_context);
                    main_goal = (uu___85_808.main_goal);
                    all_implicits = (uu___85_808.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___86_810 = p in
                  {
                    main_context = (uu___86_810.main_context);
                    main_goal = (uu___86_810.main_goal);
                    all_implicits = (uu___86_810.all_implicits);
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
                                                let uu___87_834 = p in
                                                {
                                                  main_context =
                                                    (uu___87_834.main_context);
                                                  main_goal =
                                                    (uu___87_834.main_goal);
                                                  all_implicits =
                                                    (uu___87_834.all_implicits);
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
let arrow_one:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.comp) option
  =
  fun t  ->
    let uu____936 =
      let uu____937 = FStar_Syntax_Subst.compress t in
      uu____937.FStar_Syntax_Syntax.n in
    match uu____936 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) -> Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____998 =
          let uu____1003 =
            let uu____1004 = FStar_Syntax_Util.arrow bs c in
            FStar_Syntax_Syntax.mk_Total uu____1004 in
          (b, uu____1003) in
        Some uu____998
    | uu____1011 -> None
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____1020 = arrow_one goal.goal_ty in
       match uu____1020 with
       | Some (b,c) ->
           let uu____1031 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1031 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1051 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1054 =
                  let uu____1055 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1055 in
                if uu____1054
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1068 =
                     FStar_TypeChecker_Util.new_implicit_var "intro"
                       typ'.FStar_Syntax_Syntax.pos env' typ' in
                   match uu____1068 with
                   | (u,uu____1079,g) ->
                       let uu____1087 =
                         let uu____1088 = FStar_Syntax_Util.abs [b1] u None in
                         FStar_TypeChecker_Rel.teq_nosmt goal.context
                           goal.witness uu____1088 in
                       if uu____1087
                       then
                         let g1 =
                           let uu____1102 =
                             FStar_TypeChecker_Rel.solve_deferred_constraints
                               goal.context g in
                           FStar_All.pipe_right uu____1102
                             FStar_TypeChecker_Rel.resolve_implicits in
                         let uu____1103 =
                           add_implicits g1.FStar_TypeChecker_Env.implicits in
                         bind uu____1103
                           (fun uu____1107  ->
                              let uu____1108 =
                                let uu____1110 =
                                  let uu___90_1111 = goal in
                                  let uu____1112 = bnorm env' u in
                                  let uu____1113 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1112;
                                    goal_ty = uu____1113
                                  } in
                                replace_cur uu____1110 in
                              bind uu____1108 (fun uu____1116  -> ret b1))
                       else fail "intro: unification failed"))
       | None  ->
           let uu____1124 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1124)
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
           let uu____1143 =
             let uu____1145 = FStar_List.map tr s in
             FStar_List.flatten uu____1145 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1143 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___91_1151 = goal in
            { context = (uu___91_1151.context); witness = w; goal_ty = t }))
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
       let uu____1163 = istrivial goal.context goal.goal_ty in
       if uu____1163
       then (solve goal FStar_Syntax_Const.exp_unit; dismiss)
       else
         (let uu____1167 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1167))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1174 =
           try
             let uu____1188 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1188
           with
           | e ->
               let uu____1201 = FStar_Syntax_Print.term_to_string t in
               let uu____1202 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1201
                 uu____1202 in
         bind uu____1174
           (fun uu____1209  ->
              match uu____1209 with
              | (t1,typ,guard) ->
                  let uu____1217 =
                    let uu____1218 =
                      let uu____1219 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1219 in
                    Prims.op_Negation uu____1218 in
                  if uu____1217
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1222 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1222
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1226 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1227 =
                          let uu____1228 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1228 in
                        let uu____1229 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1226 uu____1227 uu____1229))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1236 =
           try
             let uu____1250 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1250
           with
           | e ->
               let uu____1263 = FStar_Syntax_Print.term_to_string t in
               let uu____1264 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1263
                 uu____1264 in
         bind uu____1236
           (fun uu____1271  ->
              match uu____1271 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1284 =
                       let uu____1285 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1285 in
                     if uu____1284
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1288 =
                          let uu____1295 =
                            let uu____1301 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1301.FStar_Syntax_Syntax.effect_args in
                          match uu____1295 with
                          | pre::post::uu____1310 -> ((fst pre), (fst post))
                          | uu____1340 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1288 with
                        | (pre,post) ->
                            let uu____1363 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1363
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1366  ->
                                    add_irrelevant_goal goal.context pre))
                            else
                              (let uu____1368 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1369 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1370 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1368 uu____1369 uu____1370)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1379 =
          let uu____1383 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1383 in
        FStar_List.map FStar_Pervasives.fst uu____1379 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1406 = let uu____1409 = exact tm in trytac uu____1409 in
           bind uu____1406
             (fun r  ->
                match r with
                | Some r1 -> ret ()
                | None  ->
                    let uu____1416 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1416 with
                     | (tm1,typ,guard) ->
                         let uu____1424 =
                           let uu____1425 =
                             let uu____1426 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1426 in
                           Prims.op_Negation uu____1425 in
                         if uu____1424
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1429 = arrow_one typ in
                            match uu____1429 with
                            | None  ->
                                let uu____1436 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1436
                            | Some ((bv,aq),uu____1439) ->
                                let uu____1446 =
                                  FStar_TypeChecker_Util.new_implicit_var
                                    "apply"
                                    (goal.goal_ty).FStar_Syntax_Syntax.pos
                                    goal.context bv.FStar_Syntax_Syntax.sort in
                                (match uu____1446 with
                                 | (u,uu____1455,g_u) ->
                                     let tm' =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1
                                         [(u, aq)] None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let uu____1472 = __apply uopt tm' in
                                     bind uu____1472
                                       (fun uu____1474  ->
                                          let g_u1 =
                                            let uu____1476 =
                                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                                goal.context g_u in
                                            FStar_All.pipe_right uu____1476
                                              FStar_TypeChecker_Rel.resolve_implicits in
                                          let uu____1477 =
                                            let uu____1478 =
                                              let uu____1481 =
                                                let uu____1482 =
                                                  FStar_Syntax_Util.head_and_args
                                                    u in
                                                fst uu____1482 in
                                              FStar_Syntax_Subst.compress
                                                uu____1481 in
                                            uu____1478.FStar_Syntax_Syntax.n in
                                          match uu____1477 with
                                          | FStar_Syntax_Syntax.Tm_uvar
                                              (uvar,uu____1501) ->
                                              let uu____1514 =
                                                add_implicits
                                                  g_u1.FStar_TypeChecker_Env.implicits in
                                              bind uu____1514
                                                (fun uu____1516  ->
                                                   bind get
                                                     (fun ps  ->
                                                        let uu____1518 =
                                                          uopt &&
                                                            (uvar_free uvar
                                                               ps) in
                                                        if uu____1518
                                                        then ret ()
                                                        else
                                                          (let uu____1521 =
                                                             let uu____1523 =
                                                               let uu____1524
                                                                 =
                                                                 bnorm
                                                                   goal.context
                                                                   u in
                                                               let uu____1525
                                                                 =
                                                                 bnorm
                                                                   goal.context
                                                                   bv.FStar_Syntax_Syntax.sort in
                                                               {
                                                                 context =
                                                                   (goal.context);
                                                                 witness =
                                                                   uu____1524;
                                                                 goal_ty =
                                                                   uu____1525
                                                               } in
                                                             [uu____1523] in
                                                           add_goals
                                                             uu____1521)))
                                          | uu____1526 -> ret ()))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1532 = __apply true tm in focus_cur_goal uu____1532
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1540 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1540 with
         | (tm1,t,guard) ->
             let uu____1548 =
               let uu____1549 =
                 let uu____1550 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1550 in
               Prims.op_Negation uu____1549 in
             if uu____1548
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1553 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____1553 with
                | (bs,comp) ->
                    let uu____1568 =
                      FStar_List.fold_left
                        (fun uu____1585  ->
                           fun uu____1586  ->
                             match (uu____1585, uu____1586) with
                             | ((uvs,guard1,subst1),(b,aq)) ->
                                 let b_t =
                                   FStar_Syntax_Subst.subst subst1
                                     b.FStar_Syntax_Syntax.sort in
                                 let uu____1635 =
                                   FStar_TypeChecker_Util.new_implicit_var
                                     "apply_lemma"
                                     (goal.goal_ty).FStar_Syntax_Syntax.pos
                                     goal.context b_t in
                                 (match uu____1635 with
                                  | (u,uu____1650,g_u) ->
                                      let uu____1658 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard1 g_u in
                                      (((u, aq) :: uvs), uu____1658,
                                        ((FStar_Syntax_Syntax.NT (b, u)) ::
                                        subst1)))) ([], guard, []) bs in
                    (match uu____1568 with
                     | (uvs,implicits,subst1) ->
                         let uvs1 = FStar_List.rev uvs in
                         let comp1 =
                           FStar_Syntax_Subst.subst_comp subst1 comp in
                         let uu____1690 =
                           let uu____1697 =
                             let uu____1703 =
                               FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             uu____1703.FStar_Syntax_Syntax.effect_args in
                           match uu____1697 with
                           | pre::post::uu____1712 -> ((fst pre), (fst post))
                           | uu____1742 ->
                               failwith
                                 "apply_lemma: impossible: not a lemma" in
                         (match uu____1690 with
                          | (pre,post) ->
                              let uu____1765 =
                                let uu____1767 =
                                  FStar_Syntax_Util.mk_squash post in
                                FStar_TypeChecker_Rel.try_teq false
                                  goal.context uu____1767 goal.goal_ty in
                              (match uu____1765 with
                               | None  ->
                                   let uu____1769 =
                                     let uu____1770 =
                                       FStar_Syntax_Util.mk_squash post in
                                     FStar_Syntax_Print.term_to_string
                                       uu____1770 in
                                   let uu____1771 =
                                     FStar_Syntax_Print.term_to_string
                                       goal.goal_ty in
                                   fail2
                                     "apply_lemma: does not unify with goal: %s vs %s"
                                     uu____1769 uu____1771
                               | Some g ->
                                   let g1 =
                                     let uu____1774 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         goal.context g in
                                     FStar_All.pipe_right uu____1774
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   let solution =
                                     FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                       None
                                       (goal.context).FStar_TypeChecker_Env.range in
                                   let implicits1 =
                                     FStar_All.pipe_right
                                       implicits.FStar_TypeChecker_Env.implicits
                                       (FStar_List.filter
                                          (fun uu____1808  ->
                                             match uu____1808 with
                                             | (uu____1815,uu____1816,uu____1817,tm2,uu____1819,uu____1820)
                                                 ->
                                                 let uu____1821 =
                                                   FStar_Syntax_Util.head_and_args
                                                     tm2 in
                                                 (match uu____1821 with
                                                  | (hd1,uu____1832) ->
                                                      let uu____1847 =
                                                        let uu____1848 =
                                                          FStar_Syntax_Subst.compress
                                                            hd1 in
                                                        uu____1848.FStar_Syntax_Syntax.n in
                                                      (match uu____1847 with
                                                       | FStar_Syntax_Syntax.Tm_uvar
                                                           uu____1851 -> true
                                                       | uu____1860 -> false)))) in
                                   (solve goal solution;
                                    (let is_free_uvar uv t1 =
                                       let free_uvars =
                                         let uu____1871 =
                                           let uu____1875 =
                                             FStar_Syntax_Free.uvars t1 in
                                           FStar_Util.set_elements uu____1875 in
                                         FStar_List.map FStar_Pervasives.fst
                                           uu____1871 in
                                       FStar_List.existsML
                                         (fun u  ->
                                            FStar_Syntax_Unionfind.equiv u uv)
                                         free_uvars in
                                     let appears uv goals =
                                       FStar_List.existsML
                                         (fun g'  ->
                                            is_free_uvar uv g'.goal_ty) goals in
                                     let checkone t1 goals =
                                       let uu____1903 =
                                         FStar_Syntax_Util.head_and_args t1 in
                                       match uu____1903 with
                                       | (hd1,uu____1914) ->
                                           (match hd1.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                (uv,uu____1930) ->
                                                appears uv goals
                                            | uu____1943 -> false) in
                                     let sub_goals =
                                       FStar_All.pipe_right implicits1
                                         (FStar_List.map
                                            (fun uu____1960  ->
                                               match uu____1960 with
                                               | (_msg,_env,_uvar,term,typ,uu____1972)
                                                   ->
                                                   let uu____1973 =
                                                     bnorm goal.context term in
                                                   let uu____1974 =
                                                     bnorm goal.context typ in
                                                   {
                                                     context = (goal.context);
                                                     witness = uu____1973;
                                                     goal_ty = uu____1974
                                                   })) in
                                     let rec filter' f xs =
                                       match xs with
                                       | [] -> []
                                       | x::xs1 ->
                                           let uu____2006 = f x xs1 in
                                           if uu____2006
                                           then
                                             let uu____2008 = filter' f xs1 in
                                             x :: uu____2008
                                           else filter' f xs1 in
                                     let sub_goals1 =
                                       filter'
                                         (fun g2  ->
                                            fun goals  ->
                                              let uu____2016 =
                                                checkone g2.witness goals in
                                              Prims.op_Negation uu____2016)
                                         sub_goals in
                                     let uu____2017 =
                                       add_irrelevant_goal goal.context pre in
                                     bind uu____2017
                                       (fun uu____2019  ->
                                          let uu____2020 = trytac trivial in
                                          bind uu____2020
                                            (fun uu____2024  ->
                                               let uu____2026 =
                                                 add_implicits
                                                   g1.FStar_TypeChecker_Env.implicits in
                                               bind uu____2026
                                                 (fun uu____2028  ->
                                                    bind dismiss
                                                      (fun uu____2029  ->
                                                         add_goals sub_goals1)))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2036 =
           FStar_All.pipe_left mlog
             (fun uu____2041  ->
                let uu____2042 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2043 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2042
                  uu____2043) in
         bind uu____2036
           (fun uu____2044  ->
              let uu____2045 =
                let uu____2047 =
                  let uu____2048 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2048 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2047 in
              match uu____2045 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2055::(x,uu____2057)::(e,uu____2059)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2093 =
                    let uu____2094 = FStar_Syntax_Subst.compress x in
                    uu____2094.FStar_Syntax_Syntax.n in
                  (match uu____2093 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___96_2100 = goal in
                         let uu____2101 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2104 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___96_2100.context);
                           witness = uu____2101;
                           goal_ty = uu____2104
                         } in
                       replace_cur goal1
                   | uu____2107 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2108 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2112 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2112 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2127 = FStar_Util.set_mem x fns_ty in
           if uu____2127
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2130 =
                FStar_TypeChecker_Util.new_implicit_var "clear"
                  (goal.goal_ty).FStar_Syntax_Syntax.pos env' goal.goal_ty in
              match uu____2130 with
              | (u,uu____2139,g) ->
                  let uu____2147 =
                    let uu____2148 =
                      FStar_TypeChecker_Rel.teq_nosmt goal.context
                        goal.witness u in
                    Prims.op_Negation uu____2148 in
                  if uu____2147
                  then fail "clear: unification failed"
                  else
                    (let new_goal =
                       let uu___97_2152 = goal in
                       let uu____2153 = bnorm env' u in
                       {
                         context = env';
                         witness = uu____2153;
                         goal_ty = (uu___97_2152.goal_ty)
                       } in
                     let g1 =
                       let uu____2155 =
                         FStar_TypeChecker_Rel.solve_deferred_constraints
                           goal.context g in
                       FStar_All.pipe_right uu____2155
                         FStar_TypeChecker_Rel.resolve_implicits in
                     bind dismiss
                       (fun uu____2156  ->
                          let uu____2157 =
                            add_implicits g1.FStar_TypeChecker_Env.implicits in
                          bind uu____2157
                            (fun uu____2159  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2166 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2166 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2181 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2181 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2195 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2195 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___98_2218 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2225 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2225 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2237 = FStar_Syntax_Print.bv_to_string x in
               let uu____2238 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2237 uu____2238
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2251 = revert_all_hd xs1 in
        bind uu____2251 (fun uu____2253  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___99_2263 = g in
           {
             context = ctx';
             witness = (uu___99_2263.witness);
             goal_ty = (uu___99_2263.goal_ty)
           } in
         bind dismiss (fun uu____2264  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___100_2274 = g in
           {
             context = ctx';
             witness = (uu___100_2274.witness);
             goal_ty = (uu___100_2274.goal_ty)
           } in
         bind dismiss (fun uu____2275  -> add_goals [g']))
let rec bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2296 = FStar_Syntax_Subst.compress t in
          uu____2296.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2319 =
                let uu____2329 = ff hd1 in
                let uu____2330 =
                  FStar_List.map
                    (fun uu____2338  ->
                       match uu____2338 with
                       | (a,q) -> let uu____2345 = ff a in (uu____2345, q))
                    args in
                (uu____2329, uu____2330) in
              FStar_Syntax_Syntax.Tm_app uu____2319
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2374 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2374 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2380 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2380 t' in
                   let uu____2381 =
                     let uu____2396 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2396, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2381)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2415 -> tn in
        f env
          (let uu___101_2416 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___101_2416.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos =
               (uu___101_2416.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___101_2416.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2450 = f x in
      bind uu____2450
        (fun y  ->
           let uu____2454 = mapM f xs in
           bind uu____2454 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2486 = FStar_Syntax_Subst.compress t in
          uu____2486.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2512 = ff hd1 in
              bind uu____2512
                (fun hd2  ->
                   let fa uu____2523 =
                     match uu____2523 with
                     | (a,q) ->
                         let uu____2531 = ff a in
                         bind uu____2531 (fun a1  -> ret (a1, q)) in
                   let uu____2538 = mapM fa args in
                   bind uu____2538
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2582 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2582 with
               | (bs1,t') ->
                   let uu____2588 =
                     let uu____2590 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2590 t' in
                   bind uu____2588
                     (fun t''  ->
                        let uu____2592 =
                          let uu____2593 =
                            let uu____2608 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2608, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2593 in
                        ret uu____2592))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2627 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___102_2629 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___102_2629.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___102_2629.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___102_2629.FStar_Syntax_Syntax.vars)
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
          let uu____2650 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2650 with
          | (t1,lcomp,g) ->
              let uu____2658 =
                (let uu____2659 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2659) ||
                  (let uu____2660 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2660) in
              if uu____2658
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2666 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env typ in
                 match uu____2666 with
                 | (ut,uvs,guard) ->
                     (log ps
                        (fun uu____2684  ->
                           let uu____2685 =
                             FStar_Syntax_Print.term_to_string t1 in
                           let uu____2686 =
                             FStar_Syntax_Print.term_to_string ut in
                           FStar_Util.print2
                             "Pointwise_rec: making equality %s = %s\n"
                             uu____2685 uu____2686);
                      (let uu____2687 =
                         let uu____2689 =
                           let uu____2690 =
                             FStar_TypeChecker_TcTerm.universe_of env typ in
                           FStar_Syntax_Util.mk_eq2 uu____2690 typ t1 ut in
                         add_irrelevant_goal env uu____2689 in
                       bind uu____2687
                         (fun uu____2691  ->
                            let uu____2692 =
                              bind tau
                                (fun uu____2694  ->
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env guard;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.WHNF]
                                        env ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2692))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2705 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2705 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2726  ->
                   let uu____2727 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2727);
              bind dismiss_all
                (fun uu____2728  ->
                   let uu____2729 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2729
                     (fun gt'  ->
                        log ps
                          (fun uu____2733  ->
                             let uu____2734 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2734);
                        (let uu____2735 = push_goals gs in
                         bind uu____2735
                           (fun uu____2737  ->
                              add_goals
                                [(let uu___103_2738 = g in
                                  {
                                    context = (uu___103_2738.context);
                                    witness = (uu___103_2738.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2741 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2741 with
       | Some t ->
           let uu____2751 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2751 with
            | (hd1,args) ->
                let uu____2772 =
                  let uu____2780 =
                    let uu____2781 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2781.FStar_Syntax_Syntax.n in
                  (uu____2780, args) in
                (match uu____2772 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2791::(l,uu____2793)::(r,uu____2795)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.eq2_lid
                     ->
                     let l1 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.Delta_constant] g.context l in
                     let r1 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.Delta_constant] g.context r in
                     let uu____2831 =
                       let uu____2832 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l1 r1 in
                       Prims.op_Negation uu____2832 in
                     if uu____2831
                     then
                       let uu____2834 = FStar_Syntax_Print.term_to_string l1 in
                       let uu____2835 = FStar_Syntax_Print.term_to_string r1 in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____2834 uu____2835
                     else
                       (let t_unit1 = FStar_TypeChecker_Common.t_unit in
                        solve g t_unit1; dismiss)
                 | (hd2,uu____2842) ->
                     let uu____2853 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____2853))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___104_2863 = ps in
              {
                main_context = (uu___104_2863.main_context);
                main_goal = (uu___104_2863.main_goal);
                all_implicits = (uu___104_2863.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___104_2863.smt_goals)
              })
       | uu____2864 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___105_2872 = ps in
              {
                main_context = (uu___105_2872.main_context);
                main_goal = (uu___105_2872.main_goal);
                all_implicits = (uu___105_2872.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___105_2872.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2876 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2890 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2890 with
         | (t1,typ,guard) ->
             let uu____2900 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2900 with
              | (hd1,args) ->
                  let uu____2929 =
                    let uu____2937 =
                      let uu____2938 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2938.FStar_Syntax_Syntax.n in
                    (uu____2937, args) in
                  (match uu____2929 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2951)::(q,uu____2953)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___106_2982 = g in
                         let uu____2983 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2983;
                           witness = (uu___106_2982.witness);
                           goal_ty = (uu___106_2982.goal_ty)
                         } in
                       let g2 =
                         let uu___107_2985 = g in
                         let uu____2986 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2986;
                           witness = (uu___107_2985.witness);
                           goal_ty = (uu___107_2985.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____2989  ->
                            let uu____2990 = add_goals [g1; g2] in
                            bind uu____2990
                              (fun uu____2994  ->
                                 let uu____2995 =
                                   let uu____2998 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____2999 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____2998, uu____2999) in
                                 ret uu____2995))
                   | uu____3002 ->
                       let uu____3010 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____3010)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____3016 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____3020 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____3024 -> false
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
      let uu____3044 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____3044 with
      | (u,uu____3052,g_u) ->
          let g = { context = env; witness = u; goal_ty = typ } in
          {
            main_context = env;
            main_goal = g;
            all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
            goals = [g];
            smt_goals = []
          }