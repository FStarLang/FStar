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
let __proj__Mkgoal__item__context: goal -> env =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty;_} -> __fname__context
let __proj__Mkgoal__item__witness: goal -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty;_} -> __fname__witness
let __proj__Mkgoal__item__goal_ty: goal -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty;_} -> __fname__goal_ty
type proofstate =
  {
  main_context: env;
  main_goal: goal;
  all_implicits: implicits;
  goals: goal Prims.list;
  smt_goals: goal Prims.list;}
let __proj__Mkproofstate__item__main_context: proofstate -> env =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__main_context
let __proj__Mkproofstate__item__main_goal: proofstate -> goal =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__main_goal
let __proj__Mkproofstate__item__all_implicits: proofstate -> implicits =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__all_implicits
let __proj__Mkproofstate__item__goals: proofstate -> goal Prims.list =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__goals
let __proj__Mkproofstate__item__smt_goals: proofstate -> goal Prims.list =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__smt_goals
type 'a result =
  | Success of ('a* proofstate)
  | Failed of (Prims.string* proofstate)
let uu___is_Success projectee =
  match projectee with | Success _0 -> true | uu____142 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success _0 -> _0
let uu___is_Failed projectee =
  match projectee with | Failed _0 -> true | uu____173 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed _0 -> _0
exception TacFailure of Prims.string
let uu___is_TacFailure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | TacFailure uu____198 -> true | uu____199 -> false
let __proj__TacFailure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | TacFailure uu____206 -> uu____206
type 'a tac = {
  tac_f: proofstate -> 'a result;}
let __proj__Mktac__item__tac_f projectee =
  match projectee with | { tac_f = __fname__tac_f;_} -> __fname__tac_f
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
      let uu____313 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____313
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____314 = FStar_Syntax_Print.term_to_string g.witness in
    let uu____315 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____314 uu____315
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____325 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____325
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____335 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____335
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____348 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____348
let comp_to_typ:
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____353) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____361) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: goal -> Prims.bool =
  fun g  ->
    let uu____372 =
      let uu____376 =
        FStar_TypeChecker_Normalize.unfold_whnf g.context g.goal_ty in
      FStar_Syntax_Util.un_squash uu____376 in
    match uu____372 with | Some t -> true | uu____382 -> false
let dump_goal ps goal =
  let uu____399 = goal_to_string goal in tacprint uu____399
let dump_cur: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____407 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____410 = FStar_List.hd ps.goals in dump_goal ps uu____410))
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____420 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____420);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____429 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____429);
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
      let uu____469 = FStar_ST.read tac_verb_dbg in
      match uu____469 with
      | None  ->
          ((let uu____475 =
              let uu____477 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              Some uu____477 in
            FStar_ST.write tac_verb_dbg uu____475);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____503 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____503
        then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
        else ());
       Failed (msg, ps))
let fail1 msg x = let uu____518 = FStar_Util.format1 msg x in fail uu____518
let fail2 msg x y =
  let uu____537 = FStar_Util.format2 msg x y in fail uu____537
let fail3 msg x y z =
  let uu____561 = FStar_Util.format3 msg x y z in fail uu____561
let trytac t =
  mk_tac
    (fun ps  ->
       let tx = FStar_Syntax_Unionfind.new_transaction () in
       let uu____576 = run t ps in
       match uu____576 with
       | Success (a,q) ->
           (FStar_Syntax_Unionfind.commit tx; Success ((Some a), q))
       | Failed (uu____585,uu____586) ->
           (FStar_Syntax_Unionfind.rollback tx; Success (None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____595  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____602 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____602
      then ()
      else
        (let uu____604 =
           let uu____605 =
             let uu____606 = FStar_Syntax_Print.term_to_string solution in
             let uu____607 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____608 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____606
               uu____607 uu____608 in
           TacFailure uu____605 in
         raise uu____604)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____611 =
         let uu___77_612 = p in
         let uu____613 = FStar_List.tl p.goals in
         {
           main_context = (uu___77_612.main_context);
           main_goal = (uu___77_612.main_goal);
           all_implicits = (uu___77_612.all_implicits);
           goals = uu____613;
           smt_goals = (uu___77_612.smt_goals)
         } in
       set uu____611)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___78_617 = p in
          {
            main_context = (uu___78_617.main_context);
            main_goal = (uu___78_617.main_goal);
            all_implicits = (uu___78_617.all_implicits);
            goals = [];
            smt_goals = (uu___78_617.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___79_626 = p in
            {
              main_context = (uu___79_626.main_context);
              main_goal = (uu___79_626.main_goal);
              all_implicits = (uu___79_626.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___79_626.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_635 = p in
            {
              main_context = (uu___80_635.main_context);
              main_goal = (uu___80_635.main_goal);
              all_implicits = (uu___80_635.all_implicits);
              goals = (uu___80_635.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_644 = p in
            {
              main_context = (uu___81_644.main_context);
              main_goal = (uu___81_644.main_goal);
              all_implicits = (uu___81_644.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___81_644.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_653 = p in
            {
              main_context = (uu___82_653.main_context);
              main_goal = (uu___82_653.main_goal);
              all_implicits = (uu___82_653.all_implicits);
              goals = (uu___82_653.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____659  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___83_666 = p in
            {
              main_context = (uu___83_666.main_context);
              main_goal = (uu___83_666.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___83_666.goals);
              smt_goals = (uu___83_666.smt_goals)
            }))
let new_uvar:
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term* FStar_TypeChecker_Env.guard_t) tac
  =
  fun env  ->
    fun typ  ->
      let uu____685 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____685 with
      | (u,uu____696,g_u) ->
          let uu____704 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____704 (fun uu____708  -> ret (u, g_u))
let add_irrelevant_goal: env -> FStar_Syntax_Syntax.typ -> Prims.unit tac =
  fun env  ->
    fun phi  ->
      let typ = FStar_Syntax_Util.mk_squash phi in
      let uu____722 = new_uvar env typ in
      bind uu____722
        (fun uu____728  ->
           match uu____728 with
           | (u,g_u) ->
               let goal = { context = env; witness = u; goal_ty = typ } in
               add_goals [goal])
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____738 = FStar_Syntax_Util.un_squash t in
    match uu____738 with
    | Some t' ->
        let uu____747 =
          let uu____748 = FStar_Syntax_Subst.compress t' in
          uu____748.FStar_Syntax_Syntax.n in
        (match uu____747 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____752 -> false)
    | uu____753 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____760 = FStar_Syntax_Util.un_squash t in
    match uu____760 with
    | Some t' ->
        let uu____769 =
          let uu____770 = FStar_Syntax_Subst.compress t' in
          uu____770.FStar_Syntax_Syntax.n in
        (match uu____769 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____774 -> false)
    | uu____775 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____787 = is_irrelevant g in
       if uu____787
       then bind dismiss (fun uu____789  -> add_smt_goals [g])
       else
         (let uu____791 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____791))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____821 =
         try let uu____838 = FStar_List.splitAt n1 p.goals in ret uu____838
         with | uu____853 -> fail "divide: not enough goals" in
       bind uu____821
         (fun uu____864  ->
            match uu____864 with
            | (lgs,rgs) ->
                let lp =
                  let uu___84_879 = p in
                  {
                    main_context = (uu___84_879.main_context);
                    main_goal = (uu___84_879.main_goal);
                    all_implicits = (uu___84_879.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___85_881 = p in
                  {
                    main_context = (uu___85_881.main_context);
                    main_goal = (uu___85_881.main_goal);
                    all_implicits = (uu___85_881.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____882 = set lp in
                bind uu____882
                  (fun uu____886  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____893 = set rp in
                               bind uu____893
                                 (fun uu____897  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___86_905 = p in
                                                {
                                                  main_context =
                                                    (uu___86_905.main_context);
                                                  main_goal =
                                                    (uu___86_905.main_goal);
                                                  all_implicits =
                                                    (uu___86_905.all_implicits);
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
                                              let uu____906 = set p' in
                                              bind uu____906
                                                (fun uu____910  -> ret (a, b))))))))))
let focus f =
  let uu____923 = divide (Prims.parse_int "1") f idtac in
  bind uu____923 (fun uu____929  -> match uu____929 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____950::uu____951 ->
           let uu____953 =
             let uu____958 = map tau in
             divide (Prims.parse_int "1") tau uu____958 in
           bind uu____953
             (fun uu____966  -> match uu____966 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____989 =
        bind t1
          (fun uu____991  ->
             let uu____992 = map t2 in
             bind uu____992 (fun uu____996  -> ret ())) in
      focus uu____989
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____1004 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1004 with
       | Some (b,c) ->
           let uu____1015 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1015 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1035 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1038 =
                  let uu____1039 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1039 in
                if uu____1038
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1052 = new_uvar env' typ' in
                   bind uu____1052
                     (fun uu____1060  ->
                        match uu____1060 with
                        | (u,g) ->
                            let uu____1068 =
                              let uu____1069 =
                                FStar_Syntax_Util.abs [b1] u None in
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                goal.witness uu____1069 in
                            if uu____1068
                            then
                              let uu____1082 =
                                let uu____1084 =
                                  let uu___89_1085 = goal in
                                  let uu____1086 = bnorm env' u in
                                  let uu____1087 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1086;
                                    goal_ty = uu____1087
                                  } in
                                replace_cur uu____1084 in
                              bind uu____1082 (fun uu____1090  -> ret b1)
                            else fail "intro: unification failed")))
       | None  ->
           let uu____1098 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1098)
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
           let uu____1117 =
             let uu____1119 = FStar_List.map tr s in
             FStar_List.flatten uu____1119 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1117 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___90_1125 = goal in
            { context = (uu___90_1125.context); witness = w; goal_ty = t }))
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
       let uu____1137 = istrivial goal.context goal.goal_ty in
       if uu____1137
       then (solve goal FStar_Syntax_Const.exp_unit; dismiss)
       else
         (let uu____1141 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1141))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1148 =
           try
             let uu____1162 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1162
           with
           | e ->
               let uu____1175 = FStar_Syntax_Print.term_to_string t in
               let uu____1176 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1175
                 uu____1176 in
         bind uu____1148
           (fun uu____1183  ->
              match uu____1183 with
              | (t1,typ,guard) ->
                  let uu____1191 =
                    let uu____1192 =
                      let uu____1193 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1193 in
                    Prims.op_Negation uu____1192 in
                  if uu____1191
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1196 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1196
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1200 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1201 =
                          let uu____1202 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1202 in
                        let uu____1203 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1200 uu____1201 uu____1203))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1210 =
           try
             let uu____1224 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1224
           with
           | e ->
               let uu____1237 = FStar_Syntax_Print.term_to_string t in
               let uu____1238 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1237
                 uu____1238 in
         bind uu____1210
           (fun uu____1245  ->
              match uu____1245 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1258 =
                       let uu____1259 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1259 in
                     if uu____1258
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1262 =
                          let uu____1269 =
                            let uu____1275 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1275.FStar_Syntax_Syntax.effect_args in
                          match uu____1269 with
                          | pre::post::uu____1284 -> ((fst pre), (fst post))
                          | uu____1314 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1262 with
                        | (pre,post) ->
                            let uu____1337 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1337
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1340  ->
                                    add_irrelevant_goal goal.context pre))
                            else
                              (let uu____1342 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1343 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1344 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1342 uu____1343 uu____1344)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1353 =
          let uu____1357 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1357 in
        FStar_List.map FStar_Pervasives.fst uu____1353 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1380 = let uu____1383 = exact tm in trytac uu____1383 in
           bind uu____1380
             (fun r  ->
                match r with
                | Some r1 -> ret ()
                | None  ->
                    let uu____1390 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1390 with
                     | (tm1,typ,guard) ->
                         let uu____1398 =
                           let uu____1399 =
                             let uu____1400 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1400 in
                           Prims.op_Negation uu____1399 in
                         if uu____1398
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1403 = FStar_Syntax_Util.arrow_one typ in
                            match uu____1403 with
                            | None  ->
                                let uu____1410 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1410
                            | Some ((bv,aq),c) ->
                                let uu____1420 =
                                  let uu____1421 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____1421 in
                                if uu____1420
                                then fail "apply: not total"
                                else
                                  (let uu____1424 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____1424
                                     (fun uu____1430  ->
                                        match uu____1430 with
                                        | (u,g_u) ->
                                            let tm' =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                tm1 [(u, aq)] None
                                                (goal.context).FStar_TypeChecker_Env.range in
                                            let uu____1445 = __apply uopt tm' in
                                            bind uu____1445
                                              (fun uu____1447  ->
                                                 let uu____1448 =
                                                   let uu____1449 =
                                                     let uu____1452 =
                                                       let uu____1453 =
                                                         FStar_Syntax_Util.head_and_args
                                                           u in
                                                       fst uu____1453 in
                                                     FStar_Syntax_Subst.compress
                                                       uu____1452 in
                                                   uu____1449.FStar_Syntax_Syntax.n in
                                                 match uu____1448 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     (uvar,uu____1472) ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1486 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____1486
                                                          then ret ()
                                                          else
                                                            (let uu____1489 =
                                                               let uu____1491
                                                                 =
                                                                 let uu____1492
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____1493
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1492;
                                                                   goal_ty =
                                                                    uu____1493
                                                                 } in
                                                               [uu____1491] in
                                                             add_goals
                                                               uu____1489))
                                                 | uu____1494 -> ret ())))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1500 = __apply true tm in focus uu____1500
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1508 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1508 with
         | (tm1,t,guard) ->
             let uu____1516 =
               let uu____1517 =
                 let uu____1518 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1518 in
               Prims.op_Negation uu____1517 in
             if uu____1516
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1521 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____1521 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____1538 =
                         FStar_List.fold_left
                           (fun uu____1555  ->
                              fun uu____1556  ->
                                match (uu____1555, uu____1556) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____1605 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____1605 with
                                     | (u,uu____1620,g_u) ->
                                         let uu____1628 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____1628,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____1538 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1660 =
                             let uu____1667 =
                               let uu____1673 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____1673.FStar_Syntax_Syntax.effect_args in
                             match uu____1667 with
                             | pre::post::uu____1682 ->
                                 ((fst pre), (fst post))
                             | uu____1712 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____1660 with
                            | (pre,post) ->
                                let uu____1735 =
                                  let uu____1737 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____1737 goal.goal_ty in
                                (match uu____1735 with
                                 | None  ->
                                     let uu____1739 =
                                       let uu____1740 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____1740 in
                                     let uu____1741 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____1739 uu____1741
                                 | Some g ->
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1776  ->
                                               match uu____1776 with
                                               | (uu____1783,uu____1784,uu____1785,tm2,uu____1787,uu____1788)
                                                   ->
                                                   let uu____1789 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1789 with
                                                    | (hd1,uu____1800) ->
                                                        let uu____1815 =
                                                          let uu____1816 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1816.FStar_Syntax_Syntax.n in
                                                        (match uu____1815
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1819 ->
                                                             true
                                                         | uu____1828 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____1830  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____1840 =
                                                 let uu____1844 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____1844 in
                                               FStar_List.map
                                                 FStar_Pervasives.fst
                                                 uu____1840 in
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
                                             let uu____1872 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____1872 with
                                             | (hd1,uu____1883) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____1899) ->
                                                      appears uv goals
                                                  | uu____1912 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____1929  ->
                                                     match uu____1929 with
                                                     | (_msg,_env,_uvar,term,typ,uu____1941)
                                                         ->
                                                         let uu____1942 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____1943 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____1942;
                                                           goal_ty =
                                                             uu____1943
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____1975 = f x xs1 in
                                                 if uu____1975
                                                 then
                                                   let uu____1977 =
                                                     filter' f xs1 in
                                                   x :: uu____1977
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____1985 =
                                                      checkone g1.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____1985) sub_goals in
                                           let uu____1986 =
                                             add_irrelevant_goal goal.context
                                               pre in
                                           bind uu____1986
                                             (fun uu____1988  ->
                                                let uu____1989 =
                                                  trytac trivial in
                                                bind uu____1989
                                                  (fun uu____1993  ->
                                                     let uu____1995 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits in
                                                     bind uu____1995
                                                       (fun uu____1997  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2004 =
           FStar_All.pipe_left mlog
             (fun uu____2009  ->
                let uu____2010 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2011 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2010
                  uu____2011) in
         bind uu____2004
           (fun uu____2012  ->
              let uu____2013 =
                let uu____2015 =
                  let uu____2016 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2016 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2015 in
              match uu____2013 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2023::(x,uu____2025)::(e,uu____2027)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2061 =
                    let uu____2062 = FStar_Syntax_Subst.compress x in
                    uu____2062.FStar_Syntax_Syntax.n in
                  (match uu____2061 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___95_2068 = goal in
                         let uu____2069 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2072 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___95_2068.context);
                           witness = uu____2069;
                           goal_ty = uu____2072
                         } in
                       replace_cur goal1
                   | uu____2075 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2076 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2080 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2080 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2095 = FStar_Util.set_mem x fns_ty in
           if uu____2095
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2098 = new_uvar env' goal.goal_ty in
              bind uu____2098
                (fun uu____2104  ->
                   match uu____2104 with
                   | (u,g) ->
                       let uu____2110 =
                         let uu____2111 =
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness u in
                         Prims.op_Negation uu____2111 in
                       if uu____2110
                       then fail "clear: unification failed"
                       else
                         (let new_goal =
                            let uu___96_2115 = goal in
                            let uu____2116 = bnorm env' u in
                            {
                              context = env';
                              witness = uu____2116;
                              goal_ty = (uu___96_2115.goal_ty)
                            } in
                          bind dismiss
                            (fun uu____2117  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2124 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2124 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2139 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2139 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2153 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2153 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___97_2176 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2183 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2183 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2195 = FStar_Syntax_Print.bv_to_string x in
               let uu____2196 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2195 uu____2196
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2209 = revert_all_hd xs1 in
        bind uu____2209 (fun uu____2211  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___98_2221 = g in
           {
             context = ctx';
             witness = (uu___98_2221.witness);
             goal_ty = (uu___98_2221.goal_ty)
           } in
         bind dismiss (fun uu____2222  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___99_2232 = g in
           {
             context = ctx';
             witness = (uu___99_2232.witness);
             goal_ty = (uu___99_2232.goal_ty)
           } in
         bind dismiss (fun uu____2233  -> add_goals [g']))
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2263 = f x in
      bind uu____2263
        (fun y  ->
           let uu____2267 = mapM f xs in
           bind uu____2267 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2299 = FStar_Syntax_Subst.compress t in
          uu____2299.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2325 = ff hd1 in
              bind uu____2325
                (fun hd2  ->
                   let fa uu____2336 =
                     match uu____2336 with
                     | (a,q) ->
                         let uu____2344 = ff a in
                         bind uu____2344 (fun a1  -> ret (a1, q)) in
                   let uu____2351 = mapM fa args in
                   bind uu____2351
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2395 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2395 with
               | (bs1,t') ->
                   let uu____2401 =
                     let uu____2403 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2403 t' in
                   bind uu____2401
                     (fun t''  ->
                        let uu____2405 =
                          let uu____2406 =
                            let uu____2421 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____2422 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____2421, uu____2422, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2406 in
                        ret uu____2405))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2441 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___100_2443 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___100_2443.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___100_2443.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___100_2443.FStar_Syntax_Syntax.vars)
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
          let uu____2464 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2464 with
          | (t1,lcomp,g) ->
              let uu____2472 =
                (let uu____2473 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2473) ||
                  (let uu____2474 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2474) in
              if uu____2472
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2480 = new_uvar env typ in
                 bind uu____2480
                   (fun uu____2486  ->
                      match uu____2486 with
                      | (ut,guard) ->
                          (log ps
                             (fun uu____2493  ->
                                let uu____2494 =
                                  FStar_Syntax_Print.term_to_string t1 in
                                let uu____2495 =
                                  FStar_Syntax_Print.term_to_string ut in
                                FStar_Util.print2
                                  "Pointwise_rec: making equality %s = %s\n"
                                  uu____2494 uu____2495);
                           (let uu____2496 =
                              let uu____2498 =
                                let uu____2499 =
                                  FStar_TypeChecker_TcTerm.universe_of env
                                    typ in
                                FStar_Syntax_Util.mk_eq2 uu____2499 typ t1 ut in
                              add_irrelevant_goal env uu____2498 in
                            bind uu____2496
                              (fun uu____2500  ->
                                 let uu____2501 =
                                   bind tau
                                     (fun uu____2503  ->
                                        FStar_TypeChecker_Rel.force_trivial_guard
                                          env guard;
                                        (let ut1 =
                                           FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                             env ut in
                                         ret ut1)) in
                                 focus uu____2501)))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2514 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2514 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2535  ->
                   let uu____2536 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2536);
              bind dismiss_all
                (fun uu____2537  ->
                   let uu____2538 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2538
                     (fun gt'  ->
                        log ps
                          (fun uu____2542  ->
                             let uu____2543 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2543);
                        (let uu____2544 = push_goals gs in
                         bind uu____2544
                           (fun uu____2546  ->
                              add_goals
                                [(let uu___101_2547 = g in
                                  {
                                    context = (uu___101_2547.context);
                                    witness = (uu___101_2547.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2550 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2550 with
       | Some t ->
           let uu____2560 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2560 with
            | (hd1,args) ->
                let uu____2581 =
                  let uu____2589 =
                    let uu____2590 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2590.FStar_Syntax_Syntax.n in
                  (uu____2589, args) in
                (match uu____2581 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2600::(l,uu____2602)::(r,uu____2604)::[]) when
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
                     let uu____2640 =
                       let uu____2641 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l1 r1 in
                       Prims.op_Negation uu____2641 in
                     if uu____2640
                     then
                       let uu____2643 = FStar_Syntax_Print.term_to_string l1 in
                       let uu____2644 = FStar_Syntax_Print.term_to_string r1 in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____2643 uu____2644
                     else (solve g FStar_Syntax_Const.exp_unit; dismiss)
                 | (hd2,uu____2648) ->
                     let uu____2659 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____2659))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___102_2669 = ps in
              {
                main_context = (uu___102_2669.main_context);
                main_goal = (uu___102_2669.main_goal);
                all_implicits = (uu___102_2669.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___102_2669.smt_goals)
              })
       | uu____2670 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___103_2678 = ps in
              {
                main_context = (uu___103_2678.main_context);
                main_goal = (uu___103_2678.main_goal);
                all_implicits = (uu___103_2678.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___103_2678.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2682 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2696 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2696 with
         | (t1,typ,guard) ->
             let uu____2706 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2706 with
              | (hd1,args) ->
                  let uu____2735 =
                    let uu____2743 =
                      let uu____2744 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2744.FStar_Syntax_Syntax.n in
                    (uu____2743, args) in
                  (match uu____2735 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2757)::(q,uu____2759)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___104_2788 = g in
                         let uu____2789 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2789;
                           witness = (uu___104_2788.witness);
                           goal_ty = (uu___104_2788.goal_ty)
                         } in
                       let g2 =
                         let uu___105_2791 = g in
                         let uu____2792 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2792;
                           witness = (uu___105_2791.witness);
                           goal_ty = (uu___105_2791.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____2795  ->
                            let uu____2796 = add_goals [g1; g2] in
                            bind uu____2796
                              (fun uu____2800  ->
                                 let uu____2801 =
                                   let uu____2804 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____2805 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____2804, uu____2805) in
                                 ret uu____2801))
                   | uu____2808 ->
                       let uu____2816 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____2816)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2822 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2826 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2830 -> false
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
      FStar_Syntax_Syntax.syntax -> (proofstate* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      let uu____2852 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____2852 with
      | (u,uu____2862,g_u) ->
          let g = { context = env; witness = u; goal_ty = typ } in
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            } in
          (ps, u)
let cur_env: env tac =
  bind get
    (fun ps  ->
       let uu____2874 =
         let uu____2875 = FStar_List.hd ps.goals in uu____2875.context in
       FStar_All.pipe_left ret uu____2874)
let cur_goal': FStar_Syntax_Syntax.typ tac =
  bind get
    (fun ps  ->
       let uu____2879 =
         let uu____2880 = FStar_List.hd ps.goals in uu____2880.goal_ty in
       FStar_All.pipe_left ret uu____2879)
let cur_witness: FStar_Syntax_Syntax.term tac =
  bind get
    (fun ps  ->
       let uu____2884 =
         let uu____2885 = FStar_List.hd ps.goals in uu____2885.witness in
       FStar_All.pipe_left ret uu____2884)