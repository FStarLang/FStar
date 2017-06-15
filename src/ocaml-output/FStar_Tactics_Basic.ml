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
    let uu____372 = FStar_Syntax_Util.un_squash g.goal_ty in
    match uu____372 with | Some t -> true | uu____381 -> false
let dump_goal ps goal =
  let uu____398 = goal_to_string goal in tacprint uu____398
let dump_cur: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____406 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____409 = FStar_List.hd ps.goals in dump_goal ps uu____409))
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____419 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____419);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____428 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____428);
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
      let uu____468 = FStar_ST.read tac_verb_dbg in
      match uu____468 with
      | None  ->
          ((let uu____474 =
              let uu____476 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              Some uu____476 in
            FStar_ST.write tac_verb_dbg uu____474);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____502 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____502
        then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
        else ());
       Failed (msg, ps))
let fail1 msg x = let uu____517 = FStar_Util.format1 msg x in fail uu____517
let fail2 msg x y =
  let uu____536 = FStar_Util.format2 msg x y in fail uu____536
let fail3 msg x y z =
  let uu____560 = FStar_Util.format3 msg x y z in fail uu____560
let trytac t =
  mk_tac
    (fun ps  ->
       let tx = FStar_Syntax_Unionfind.new_transaction () in
       let uu____575 = run t ps in
       match uu____575 with
       | Success (a,q) ->
           (FStar_Syntax_Unionfind.commit tx; Success ((Some a), q))
       | Failed (uu____584,uu____585) ->
           (FStar_Syntax_Unionfind.rollback tx; Success (None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____594  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____601 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____601
      then ()
      else
        (let uu____603 =
           let uu____604 =
             let uu____605 = FStar_Syntax_Print.term_to_string solution in
             let uu____606 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____607 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____605
               uu____606 uu____607 in
           TacFailure uu____604 in
         raise uu____603)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____610 =
         let uu___78_611 = p in
         let uu____612 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_611.main_context);
           main_goal = (uu___78_611.main_goal);
           all_implicits = (uu___78_611.all_implicits);
           goals = uu____612;
           smt_goals = (uu___78_611.smt_goals)
         } in
       set uu____610)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_616 = p in
          {
            main_context = (uu___79_616.main_context);
            main_goal = (uu___79_616.main_goal);
            all_implicits = (uu___79_616.all_implicits);
            goals = [];
            smt_goals = (uu___79_616.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_625 = p in
            {
              main_context = (uu___80_625.main_context);
              main_goal = (uu___80_625.main_goal);
              all_implicits = (uu___80_625.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_625.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_634 = p in
            {
              main_context = (uu___81_634.main_context);
              main_goal = (uu___81_634.main_goal);
              all_implicits = (uu___81_634.all_implicits);
              goals = (uu___81_634.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_643 = p in
            {
              main_context = (uu___82_643.main_context);
              main_goal = (uu___82_643.main_goal);
              all_implicits = (uu___82_643.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___82_643.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_652 = p in
            {
              main_context = (uu___83_652.main_context);
              main_goal = (uu___83_652.main_goal);
              all_implicits = (uu___83_652.all_implicits);
              goals = (uu___83_652.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____658  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_665 = p in
            {
              main_context = (uu___84_665.main_context);
              main_goal = (uu___84_665.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_665.goals);
              smt_goals = (uu___84_665.smt_goals)
            }))
let add_irrelevant_goal: env -> FStar_Syntax_Syntax.typ -> Prims.unit tac =
  fun env  ->
    fun phi  ->
      let typ = FStar_Syntax_Util.mk_squash phi in
      let uu____683 =
        FStar_TypeChecker_Util.new_implicit_var "add_irrelevant_goal"
          phi.FStar_Syntax_Syntax.pos env typ in
      match uu____683 with
      | (u,uu____692,g_u) ->
          let goal = { context = env; witness = u; goal_ty = typ } in
          let uu____701 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____701 (fun uu____703  -> add_goals [goal])
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____707 = FStar_Syntax_Util.un_squash t in
    match uu____707 with
    | Some t' ->
        let uu____716 =
          let uu____717 = FStar_Syntax_Subst.compress t' in
          uu____717.FStar_Syntax_Syntax.n in
        (match uu____716 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____721 -> false)
    | uu____722 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____729 = FStar_Syntax_Util.un_squash t in
    match uu____729 with
    | Some t' ->
        let uu____738 =
          let uu____739 = FStar_Syntax_Subst.compress t' in
          uu____739.FStar_Syntax_Syntax.n in
        (match uu____738 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____743 -> false)
    | uu____744 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____756 = is_irrelevant g in
       if uu____756
       then bind dismiss (fun uu____758  -> add_smt_goals [g])
       else
         (let uu____760 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____760))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____790 =
         try let uu____807 = FStar_List.splitAt n1 p.goals in ret uu____807
         with | uu____822 -> fail "divide: not enough goals" in
       bind uu____790
         (fun uu____833  ->
            match uu____833 with
            | (lgs,rgs) ->
                let lp =
                  let uu___85_848 = p in
                  {
                    main_context = (uu___85_848.main_context);
                    main_goal = (uu___85_848.main_goal);
                    all_implicits = (uu___85_848.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___86_850 = p in
                  {
                    main_context = (uu___86_850.main_context);
                    main_goal = (uu___86_850.main_goal);
                    all_implicits = (uu___86_850.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____851 = set lp in
                bind uu____851
                  (fun uu____855  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____862 = set rp in
                               bind uu____862
                                 (fun uu____866  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___87_874 = p in
                                                {
                                                  main_context =
                                                    (uu___87_874.main_context);
                                                  main_goal =
                                                    (uu___87_874.main_goal);
                                                  all_implicits =
                                                    (uu___87_874.all_implicits);
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
                                              let uu____875 = set p' in
                                              bind uu____875
                                                (fun uu____879  -> ret (a, b))))))))))
let focus_cur_goal f =
  let uu____892 = divide (Prims.parse_int "1") f idtac in
  bind uu____892 (fun uu____898  -> match uu____898 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____919::uu____920 ->
           let uu____922 =
             let uu____927 = map tau in
             divide (Prims.parse_int "1") tau uu____927 in
           bind uu____922
             (fun uu____935  -> match uu____935 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____958 =
        bind t1
          (fun uu____960  ->
             let uu____961 = map t2 in
             bind uu____961 (fun uu____965  -> ret ())) in
      focus_cur_goal uu____958
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____973 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____973 with
       | Some (b,c) ->
           let uu____984 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____984 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1004 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1007 =
                  let uu____1008 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1008 in
                if uu____1007
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1021 =
                     FStar_TypeChecker_Util.new_implicit_var "intro"
                       typ'.FStar_Syntax_Syntax.pos env' typ' in
                   match uu____1021 with
                   | (u,uu____1032,g) ->
                       let uu____1040 =
                         let uu____1041 = FStar_Syntax_Util.abs [b1] u None in
                         FStar_TypeChecker_Rel.teq_nosmt goal.context
                           goal.witness uu____1041 in
                       if uu____1040
                       then
                         let g1 =
                           let uu____1055 =
                             FStar_TypeChecker_Rel.solve_deferred_constraints
                               goal.context g in
                           FStar_All.pipe_right uu____1055
                             FStar_TypeChecker_Rel.resolve_implicits in
                         let uu____1056 =
                           add_implicits g1.FStar_TypeChecker_Env.implicits in
                         bind uu____1056
                           (fun uu____1060  ->
                              let uu____1061 =
                                let uu____1063 =
                                  let uu___90_1064 = goal in
                                  let uu____1065 = bnorm env' u in
                                  let uu____1066 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1065;
                                    goal_ty = uu____1066
                                  } in
                                replace_cur uu____1063 in
                              bind uu____1061 (fun uu____1069  -> ret b1))
                       else fail "intro: unification failed"))
       | None  ->
           let uu____1077 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1077)
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
           let uu____1096 =
             let uu____1098 = FStar_List.map tr s in
             FStar_List.flatten uu____1098 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1096 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___91_1104 = goal in
            { context = (uu___91_1104.context); witness = w; goal_ty = t }))
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
       let uu____1116 = istrivial goal.context goal.goal_ty in
       if uu____1116
       then (solve goal FStar_Syntax_Const.exp_unit; dismiss)
       else
         (let uu____1120 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1120))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1127 =
           try
             let uu____1141 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1141
           with
           | e ->
               let uu____1154 = FStar_Syntax_Print.term_to_string t in
               let uu____1155 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1154
                 uu____1155 in
         bind uu____1127
           (fun uu____1162  ->
              match uu____1162 with
              | (t1,typ,guard) ->
                  let uu____1170 =
                    let uu____1171 =
                      let uu____1172 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1172 in
                    Prims.op_Negation uu____1171 in
                  if uu____1170
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1175 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1175
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1179 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1180 =
                          let uu____1181 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1181 in
                        let uu____1182 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1179 uu____1180 uu____1182))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1189 =
           try
             let uu____1203 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1203
           with
           | e ->
               let uu____1216 = FStar_Syntax_Print.term_to_string t in
               let uu____1217 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1216
                 uu____1217 in
         bind uu____1189
           (fun uu____1224  ->
              match uu____1224 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1237 =
                       let uu____1238 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1238 in
                     if uu____1237
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1241 =
                          let uu____1248 =
                            let uu____1254 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1254.FStar_Syntax_Syntax.effect_args in
                          match uu____1248 with
                          | pre::post::uu____1263 -> ((fst pre), (fst post))
                          | uu____1293 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1241 with
                        | (pre,post) ->
                            let uu____1316 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1316
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1319  ->
                                    add_irrelevant_goal goal.context pre))
                            else
                              (let uu____1321 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1322 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1323 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1321 uu____1322 uu____1323)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1332 =
          let uu____1336 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1336 in
        FStar_List.map FStar_Pervasives.fst uu____1332 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1359 = let uu____1362 = exact tm in trytac uu____1362 in
           bind uu____1359
             (fun r  ->
                match r with
                | Some r1 -> ret ()
                | None  ->
                    let uu____1369 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1369 with
                     | (tm1,typ,guard) ->
                         let uu____1377 =
                           let uu____1378 =
                             let uu____1379 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1379 in
                           Prims.op_Negation uu____1378 in
                         if uu____1377
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1382 = FStar_Syntax_Util.arrow_one typ in
                            match uu____1382 with
                            | None  ->
                                let uu____1389 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1389
                            | Some ((bv,aq),c) ->
                                let uu____1399 =
                                  let uu____1400 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____1400 in
                                if uu____1399
                                then fail "apply: not total"
                                else
                                  (let uu____1403 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   match uu____1403 with
                                   | (u,uu____1412,g_u) ->
                                       let tm' =
                                         FStar_Syntax_Syntax.mk_Tm_app tm1
                                           [(u, aq)] None
                                           (goal.context).FStar_TypeChecker_Env.range in
                                       let uu____1429 = __apply uopt tm' in
                                       bind uu____1429
                                         (fun uu____1431  ->
                                            let g_u1 =
                                              let uu____1433 =
                                                FStar_TypeChecker_Rel.solve_deferred_constraints
                                                  goal.context g_u in
                                              FStar_All.pipe_right uu____1433
                                                FStar_TypeChecker_Rel.resolve_implicits in
                                            let uu____1434 =
                                              let uu____1435 =
                                                let uu____1438 =
                                                  let uu____1439 =
                                                    FStar_Syntax_Util.head_and_args
                                                      u in
                                                  fst uu____1439 in
                                                FStar_Syntax_Subst.compress
                                                  uu____1438 in
                                              uu____1435.FStar_Syntax_Syntax.n in
                                            match uu____1434 with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                (uvar,uu____1458) ->
                                                let uu____1471 =
                                                  add_implicits
                                                    g_u1.FStar_TypeChecker_Env.implicits in
                                                bind uu____1471
                                                  (fun uu____1473  ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1475 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____1475
                                                          then ret ()
                                                          else
                                                            (let uu____1478 =
                                                               let uu____1480
                                                                 =
                                                                 let uu____1481
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____1482
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1481;
                                                                   goal_ty =
                                                                    uu____1482
                                                                 } in
                                                               [uu____1480] in
                                                             add_goals
                                                               uu____1478)))
                                            | uu____1483 -> ret ()))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1489 = __apply true tm in focus_cur_goal uu____1489
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1497 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1497 with
         | (tm1,t,guard) ->
             let uu____1505 =
               let uu____1506 =
                 let uu____1507 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1507 in
               Prims.op_Negation uu____1506 in
             if uu____1505
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1510 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____1510 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____1527 =
                         FStar_List.fold_left
                           (fun uu____1544  ->
                              fun uu____1545  ->
                                match (uu____1544, uu____1545) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____1594 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____1594 with
                                     | (u,uu____1609,g_u) ->
                                         let uu____1617 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____1617,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____1527 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1649 =
                             let uu____1656 =
                               let uu____1662 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____1662.FStar_Syntax_Syntax.effect_args in
                             match uu____1656 with
                             | pre::post::uu____1671 ->
                                 ((fst pre), (fst post))
                             | uu____1701 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____1649 with
                            | (pre,post) ->
                                let uu____1724 =
                                  let uu____1726 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____1726 goal.goal_ty in
                                (match uu____1724 with
                                 | None  ->
                                     let uu____1728 =
                                       let uu____1729 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____1729 in
                                     let uu____1730 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____1728 uu____1730
                                 | Some g ->
                                     let g1 =
                                       let uu____1733 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1733
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1767  ->
                                               match uu____1767 with
                                               | (uu____1774,uu____1775,uu____1776,tm2,uu____1778,uu____1779)
                                                   ->
                                                   let uu____1780 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1780 with
                                                    | (hd1,uu____1791) ->
                                                        let uu____1806 =
                                                          let uu____1807 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1807.FStar_Syntax_Syntax.n in
                                                        (match uu____1806
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1810 ->
                                                             true
                                                         | uu____1819 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____1821  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____1831 =
                                                 let uu____1835 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____1835 in
                                               FStar_List.map
                                                 FStar_Pervasives.fst
                                                 uu____1831 in
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
                                             let uu____1863 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____1863 with
                                             | (hd1,uu____1874) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____1890) ->
                                                      appears uv goals
                                                  | uu____1903 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____1920  ->
                                                     match uu____1920 with
                                                     | (_msg,_env,_uvar,term,typ,uu____1932)
                                                         ->
                                                         let uu____1933 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____1934 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____1933;
                                                           goal_ty =
                                                             uu____1934
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____1966 = f x xs1 in
                                                 if uu____1966
                                                 then
                                                   let uu____1968 =
                                                     filter' f xs1 in
                                                   x :: uu____1968
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g2  ->
                                                  fun goals  ->
                                                    let uu____1976 =
                                                      checkone g2.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____1976) sub_goals in
                                           let uu____1977 =
                                             add_irrelevant_goal goal.context
                                               pre in
                                           bind uu____1977
                                             (fun uu____1979  ->
                                                let uu____1980 =
                                                  trytac trivial in
                                                bind uu____1980
                                                  (fun uu____1984  ->
                                                     let uu____1986 =
                                                       add_implicits
                                                         g1.FStar_TypeChecker_Env.implicits in
                                                     bind uu____1986
                                                       (fun uu____1988  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____1995 =
           FStar_All.pipe_left mlog
             (fun uu____2000  ->
                let uu____2001 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2002 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2001
                  uu____2002) in
         bind uu____1995
           (fun uu____2003  ->
              let uu____2004 =
                let uu____2006 =
                  let uu____2007 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2007 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2006 in
              match uu____2004 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2014::(x,uu____2016)::(e,uu____2018)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2052 =
                    let uu____2053 = FStar_Syntax_Subst.compress x in
                    uu____2053.FStar_Syntax_Syntax.n in
                  (match uu____2052 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___96_2059 = goal in
                         let uu____2060 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2063 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___96_2059.context);
                           witness = uu____2060;
                           goal_ty = uu____2063
                         } in
                       replace_cur goal1
                   | uu____2066 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2067 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2071 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2071 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2086 = FStar_Util.set_mem x fns_ty in
           if uu____2086
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2089 =
                FStar_TypeChecker_Util.new_implicit_var "clear"
                  (goal.goal_ty).FStar_Syntax_Syntax.pos env' goal.goal_ty in
              match uu____2089 with
              | (u,uu____2098,g) ->
                  let uu____2106 =
                    let uu____2107 =
                      FStar_TypeChecker_Rel.teq_nosmt goal.context
                        goal.witness u in
                    Prims.op_Negation uu____2107 in
                  if uu____2106
                  then fail "clear: unification failed"
                  else
                    (let new_goal =
                       let uu___97_2111 = goal in
                       let uu____2112 = bnorm env' u in
                       {
                         context = env';
                         witness = uu____2112;
                         goal_ty = (uu___97_2111.goal_ty)
                       } in
                     let g1 =
                       let uu____2114 =
                         FStar_TypeChecker_Rel.solve_deferred_constraints
                           goal.context g in
                       FStar_All.pipe_right uu____2114
                         FStar_TypeChecker_Rel.resolve_implicits in
                     bind dismiss
                       (fun uu____2115  ->
                          let uu____2116 =
                            add_implicits g1.FStar_TypeChecker_Env.implicits in
                          bind uu____2116
                            (fun uu____2118  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2125 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2125 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2140 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2140 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2154 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2154 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___98_2177 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2184 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2184 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2196 = FStar_Syntax_Print.bv_to_string x in
               let uu____2197 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2196 uu____2197
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2210 = revert_all_hd xs1 in
        bind uu____2210 (fun uu____2212  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___99_2222 = g in
           {
             context = ctx';
             witness = (uu___99_2222.witness);
             goal_ty = (uu___99_2222.goal_ty)
           } in
         bind dismiss (fun uu____2223  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___100_2233 = g in
           {
             context = ctx';
             witness = (uu___100_2233.witness);
             goal_ty = (uu___100_2233.goal_ty)
           } in
         bind dismiss (fun uu____2234  -> add_goals [g']))
let rec bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2255 = FStar_Syntax_Subst.compress t in
          uu____2255.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2278 =
                let uu____2288 = ff hd1 in
                let uu____2289 =
                  FStar_List.map
                    (fun uu____2297  ->
                       match uu____2297 with
                       | (a,q) -> let uu____2304 = ff a in (uu____2304, q))
                    args in
                (uu____2288, uu____2289) in
              FStar_Syntax_Syntax.Tm_app uu____2278
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2333 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2333 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2339 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2339 t' in
                   let uu____2340 =
                     let uu____2355 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2355, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2340)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2374 -> tn in
        f env
          (let uu___101_2375 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___101_2375.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos =
               (uu___101_2375.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___101_2375.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2409 = f x in
      bind uu____2409
        (fun y  ->
           let uu____2413 = mapM f xs in
           bind uu____2413 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2445 = FStar_Syntax_Subst.compress t in
          uu____2445.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2471 = ff hd1 in
              bind uu____2471
                (fun hd2  ->
                   let fa uu____2482 =
                     match uu____2482 with
                     | (a,q) ->
                         let uu____2490 = ff a in
                         bind uu____2490 (fun a1  -> ret (a1, q)) in
                   let uu____2497 = mapM fa args in
                   bind uu____2497
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2541 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2541 with
               | (bs1,t') ->
                   let uu____2547 =
                     let uu____2549 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2549 t' in
                   bind uu____2547
                     (fun t''  ->
                        let uu____2551 =
                          let uu____2552 =
                            let uu____2567 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2567, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2552 in
                        ret uu____2551))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2586 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___102_2588 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___102_2588.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___102_2588.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___102_2588.FStar_Syntax_Syntax.vars)
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
          let uu____2609 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2609 with
          | (t1,lcomp,g) ->
              let uu____2617 =
                (let uu____2618 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2618) ||
                  (let uu____2619 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2619) in
              if uu____2617
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2625 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env typ in
                 match uu____2625 with
                 | (ut,uvs,guard) ->
                     (log ps
                        (fun uu____2643  ->
                           let uu____2644 =
                             FStar_Syntax_Print.term_to_string t1 in
                           let uu____2645 =
                             FStar_Syntax_Print.term_to_string ut in
                           FStar_Util.print2
                             "Pointwise_rec: making equality %s = %s\n"
                             uu____2644 uu____2645);
                      (let uu____2646 =
                         add_implicits g.FStar_TypeChecker_Env.implicits in
                       bind uu____2646
                         (fun uu____2648  ->
                            let uu____2649 =
                              let uu____2651 =
                                let uu____2652 =
                                  FStar_TypeChecker_TcTerm.universe_of env
                                    typ in
                                FStar_Syntax_Util.mk_eq2 uu____2652 typ t1 ut in
                              add_irrelevant_goal env uu____2651 in
                            bind uu____2649
                              (fun uu____2653  ->
                                 let uu____2654 =
                                   bind tau
                                     (fun uu____2656  ->
                                        FStar_TypeChecker_Rel.force_trivial_guard
                                          env guard;
                                        (let ut1 =
                                           FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                             env ut in
                                         ret ut1)) in
                                 focus_cur_goal uu____2654)))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2667 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2667 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2688  ->
                   let uu____2689 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2689);
              bind dismiss_all
                (fun uu____2690  ->
                   let uu____2691 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2691
                     (fun gt'  ->
                        log ps
                          (fun uu____2695  ->
                             let uu____2696 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2696);
                        (let uu____2697 = push_goals gs in
                         bind uu____2697
                           (fun uu____2699  ->
                              add_goals
                                [(let uu___103_2700 = g in
                                  {
                                    context = (uu___103_2700.context);
                                    witness = (uu___103_2700.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2703 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2703 with
       | Some t ->
           let uu____2713 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2713 with
            | (hd1,args) ->
                let uu____2734 =
                  let uu____2742 =
                    let uu____2743 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2743.FStar_Syntax_Syntax.n in
                  (uu____2742, args) in
                (match uu____2734 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2753::(l,uu____2755)::(r,uu____2757)::[]) when
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
                     let uu____2793 =
                       let uu____2794 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l1 r1 in
                       Prims.op_Negation uu____2794 in
                     if uu____2793
                     then
                       let uu____2796 = FStar_Syntax_Print.term_to_string l1 in
                       let uu____2797 = FStar_Syntax_Print.term_to_string r1 in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____2796 uu____2797
                     else (solve g FStar_Syntax_Const.exp_unit; dismiss)
                 | (hd2,uu____2801) ->
                     let uu____2812 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____2812))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___104_2822 = ps in
              {
                main_context = (uu___104_2822.main_context);
                main_goal = (uu___104_2822.main_goal);
                all_implicits = (uu___104_2822.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___104_2822.smt_goals)
              })
       | uu____2823 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___105_2831 = ps in
              {
                main_context = (uu___105_2831.main_context);
                main_goal = (uu___105_2831.main_goal);
                all_implicits = (uu___105_2831.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___105_2831.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2835 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2849 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2849 with
         | (t1,typ,guard) ->
             let uu____2859 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2859 with
              | (hd1,args) ->
                  let uu____2888 =
                    let uu____2896 =
                      let uu____2897 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2897.FStar_Syntax_Syntax.n in
                    (uu____2896, args) in
                  (match uu____2888 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2910)::(q,uu____2912)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___106_2941 = g in
                         let uu____2942 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2942;
                           witness = (uu___106_2941.witness);
                           goal_ty = (uu___106_2941.goal_ty)
                         } in
                       let g2 =
                         let uu___107_2944 = g in
                         let uu____2945 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2945;
                           witness = (uu___107_2944.witness);
                           goal_ty = (uu___107_2944.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____2948  ->
                            let uu____2949 = add_goals [g1; g2] in
                            bind uu____2949
                              (fun uu____2953  ->
                                 let uu____2954 =
                                   let uu____2957 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____2958 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____2957, uu____2958) in
                                 ret uu____2954))
                   | uu____2961 ->
                       let uu____2969 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____2969)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2975 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2979 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2983 -> false
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
      let uu____3005 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____3005 with
      | (u,uu____3015,g_u) ->
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
       let uu____3027 =
         let uu____3028 = FStar_List.hd ps.goals in uu____3028.context in
       FStar_All.pipe_left ret uu____3027)
let cur_goal': FStar_Syntax_Syntax.typ tac =
  bind get
    (fun ps  ->
       let uu____3032 =
         let uu____3033 = FStar_List.hd ps.goals in uu____3033.goal_ty in
       FStar_All.pipe_left ret uu____3032)
let cur_witness: FStar_Syntax_Syntax.term tac =
  bind get
    (fun ps  ->
       let uu____3037 =
         let uu____3038 = FStar_List.hd ps.goals in uu____3038.witness in
       FStar_All.pipe_left ret uu____3037)