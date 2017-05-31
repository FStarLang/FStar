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
  match projectee with | Success _0 -> true | uu____96 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success _0 -> _0
let uu___is_Failed projectee =
  match projectee with | Failed _0 -> true | uu____127 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed _0 -> _0
exception Failure of Prims.string
let uu___is_Failure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Failure uu____151 -> true | uu____152 -> false
let __proj__Failure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Failure uu____159 -> uu____159
type 'a tac = {
  tac_f: proofstate -> 'a result;}
let mk_tac f = { tac_f = f }
let run t p = t.tac_f p
let ret x = mk_tac (fun p  -> Success (x, p))
let bind t1 t2 =
  mk_tac
    (fun p  ->
       let uu____252 = run t1 p in
       match uu____252 with
       | Success (a,q) -> let uu____257 = t2 a in run uu____257 q
       | Failed (msg,q) -> Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____266 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____266
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____267 = FStar_Syntax_Print.term_to_string g.witness in
    let uu____268 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____267 uu____268
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____278 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____278
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____288 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____288
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____301 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____301
let comp_to_typ:
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____306) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____314) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: goal -> Prims.bool =
  fun g  ->
    let uu____325 = FStar_Syntax_Util.un_squash g.goal_ty in
    match uu____325 with | Some t -> true | uu____334 -> false
let mk_irrelevant: env -> FStar_Syntax_Syntax.typ -> goal =
  fun env  ->
    fun phi  ->
      let typ = FStar_Syntax_Util.mk_squash phi in
      let uu____347 =
        FStar_TypeChecker_Util.new_implicit_var "mk_irrelevant"
          phi.FStar_Syntax_Syntax.pos env typ in
      match uu____347 with
      | (u,uu____355,g_u) -> { context = env; witness = u; goal_ty = typ }
let dump_goal ps goal =
  let uu____376 = goal_to_string goal in tacprint uu____376
let dump_cur: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint1 "Current goal (%s):" msg;
      (let uu____385 = FStar_List.hd ps.goals in dump_goal ps uu____385)
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____395 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____395);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____401 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____401);
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
      let uu____438 = FStar_ST.read tac_verb_dbg in
      match uu____438 with
      | None  ->
          ((let uu____444 =
              let uu____446 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              Some uu____446 in
            FStar_ST.write tac_verb_dbg uu____444);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____472 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____472 then dump_proofstate ps "TACTING FAILING" else ());
       Failed (msg, ps))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____479  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____486 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____486
      then ()
      else
        (let uu____488 =
           let uu____489 =
             let uu____490 = FStar_Syntax_Print.term_to_string solution in
             let uu____491 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____492 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____490
               uu____491 uu____492 in
           Failure uu____489 in
         raise uu____488)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____495 =
         let uu___78_496 = p in
         let uu____497 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_496.main_context);
           main_goal = (uu___78_496.main_goal);
           all_implicits = (uu___78_496.all_implicits);
           goals = uu____497;
           smt_goals = (uu___78_496.smt_goals)
         } in
       set uu____495)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_501 = p in
          {
            main_context = (uu___79_501.main_context);
            main_goal = (uu___79_501.main_goal);
            all_implicits = (uu___79_501.all_implicits);
            goals = [];
            smt_goals = (uu___79_501.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_510 = p in
            {
              main_context = (uu___80_510.main_context);
              main_goal = (uu___80_510.main_goal);
              all_implicits = (uu___80_510.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_510.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_519 = p in
            {
              main_context = (uu___81_519.main_context);
              main_goal = (uu___81_519.main_goal);
              all_implicits = (uu___81_519.all_implicits);
              goals = (uu___81_519.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_528 = p in
            {
              main_context = (uu___82_528.main_context);
              main_goal = (uu___82_528.main_goal);
              all_implicits = (uu___82_528.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___82_528.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_537 = p in
            {
              main_context = (uu___83_537.main_context);
              main_goal = (uu___83_537.main_goal);
              all_implicits = (uu___83_537.all_implicits);
              goals = (uu___83_537.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____543  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_550 = p in
            {
              main_context = (uu___84_550.main_context);
              main_goal = (uu___84_550.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_550.goals);
              smt_goals = (uu___84_550.smt_goals)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____560 = FStar_Syntax_Util.un_squash t in
    match uu____560 with
    | Some t' ->
        let uu____569 =
          let uu____570 = FStar_Syntax_Subst.compress t' in
          uu____570.FStar_Syntax_Syntax.n in
        (match uu____569 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____574 -> false)
    | uu____575 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____582 = FStar_Syntax_Util.un_squash t in
    match uu____582 with
    | Some t' ->
        let uu____591 =
          let uu____592 = FStar_Syntax_Subst.compress t' in
          uu____592.FStar_Syntax_Syntax.n in
        (match uu____591 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____596 -> false)
    | uu____597 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____609 = is_irrelevant g in
       if uu____609
       then bind dismiss (fun uu____611  -> add_smt_goals [g])
       else
         (let uu____613 =
            let uu____614 = FStar_Syntax_Print.term_to_string g.goal_ty in
            FStar_Util.format1
              "goal is not irrelevant: cannot dispatch to smt (%s)" uu____614 in
          fail uu____613))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____644 =
         try let uu____661 = FStar_List.splitAt n1 p.goals in ret uu____661
         with | uu____676 -> fail "divide: not enough goals" in
       bind uu____644
         (fun uu____687  ->
            match uu____687 with
            | (lgs,rgs) ->
                let lp =
                  let uu___85_702 = p in
                  {
                    main_context = (uu___85_702.main_context);
                    main_goal = (uu___85_702.main_goal);
                    all_implicits = (uu___85_702.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___86_704 = p in
                  {
                    main_context = (uu___86_704.main_context);
                    main_goal = (uu___86_704.main_goal);
                    all_implicits = (uu___86_704.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____705 = set lp in
                bind uu____705
                  (fun uu____709  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____716 = set rp in
                               bind uu____716
                                 (fun uu____720  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___87_728 = p in
                                                {
                                                  main_context =
                                                    (uu___87_728.main_context);
                                                  main_goal =
                                                    (uu___87_728.main_goal);
                                                  all_implicits =
                                                    (uu___87_728.all_implicits);
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
                                              let uu____729 = set p' in
                                              bind uu____729
                                                (fun uu____733  -> ret (a, b))))))))))
let focus_cur_goal f =
  let uu____746 = divide (Prims.parse_int "1") f idtac in
  bind uu____746 (fun uu____752  -> match uu____752 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____773::uu____774 ->
           let uu____776 =
             let uu____781 = map tau in
             divide (Prims.parse_int "1") tau uu____781 in
           bind uu____776
             (fun uu____789  -> match uu____789 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____812 =
        bind t1
          (fun uu____814  ->
             let uu____815 = map t2 in
             bind uu____815 (fun uu____819  -> ret ())) in
      focus_cur_goal uu____812
let arrow_one:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.comp) option
  =
  fun t  ->
    let uu____830 =
      let uu____831 = FStar_Syntax_Subst.compress t in
      uu____831.FStar_Syntax_Syntax.n in
    match uu____830 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) -> Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____892 =
          let uu____897 =
            let uu____898 = FStar_Syntax_Util.arrow bs c in
            FStar_Syntax_Syntax.mk_Total uu____898 in
          (b, uu____897) in
        Some uu____892
    | uu____905 -> None
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____914 = arrow_one goal.goal_ty in
       match uu____914 with
       | Some (b,c) ->
           let uu____925 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____925 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____945 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____948 =
                  let uu____949 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____949 in
                if uu____948
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____962 =
                     FStar_TypeChecker_Util.new_implicit_var "intro"
                       typ'.FStar_Syntax_Syntax.pos env' typ' in
                   match uu____962 with
                   | (u,uu____973,g) ->
                       let uu____981 =
                         let uu____982 = FStar_Syntax_Util.abs [b1] u None in
                         FStar_TypeChecker_Rel.teq_nosmt goal.context
                           goal.witness uu____982 in
                       if uu____981
                       then
                         let uu____995 =
                           let uu____997 =
                             let uu___90_998 = goal in
                             let uu____999 = bnorm env' u in
                             let uu____1000 = bnorm env' typ' in
                             {
                               context = env';
                               witness = uu____999;
                               goal_ty = uu____1000
                             } in
                           replace_cur uu____997 in
                         bind uu____995 (fun uu____1003  -> ret b1)
                       else fail "intro: unification failed"))
       | None  -> fail "intro: goal is not an arrow")
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
           let uu____1029 =
             let uu____1031 = FStar_List.map tr s in
             FStar_List.flatten uu____1031 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1029 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___91_1037 = goal in
            { context = (uu___91_1037.context); witness = w; goal_ty = t }))
let istrivial: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.UnfoldTac] in
      let t1 = FStar_TypeChecker_Normalize.normalize steps e t in is_true t1
let trivial: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____1049 = istrivial goal.context goal.goal_ty in
       if uu____1049
       then
         let t_unit1 = FStar_TypeChecker_Common.t_unit in
         (solve goal t_unit1; dismiss)
       else
         (let uu____1056 =
            let uu____1057 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            FStar_Util.format1 "Not a trivial goal: %s" uu____1057 in
          fail uu____1056))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1064 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1064 with
         | (tm1,t,guard) ->
             let uu____1072 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1072 with
              | (bs,comp) ->
                  let uu____1087 =
                    FStar_List.fold_left
                      (fun uu____1104  ->
                         fun uu____1105  ->
                           match (uu____1104, uu____1105) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1154 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1154 with
                                | (u,uu____1169,g_u) ->
                                    let uu____1177 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1177,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1087 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let ret_typ = comp_to_typ comp1 in
                       let uu____1210 =
                         FStar_TypeChecker_Rel.try_teq false goal.context
                           ret_typ goal.goal_ty in
                       (match uu____1210 with
                        | None  ->
                            let uu____1213 =
                              let uu____1214 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____1215 =
                                FStar_Syntax_Print.term_to_string ret_typ in
                              let uu____1216 =
                                FStar_Syntax_Print.term_to_string
                                  goal.goal_ty in
                              FStar_Util.format3
                                "apply: does not unify with goal: %s : %s vs %s"
                                uu____1214 uu____1215 uu____1216 in
                            fail uu____1213
                        | Some g ->
                            let g1 =
                              let uu____1219 =
                                FStar_TypeChecker_Rel.solve_deferred_constraints
                                  goal.context g in
                              FStar_All.pipe_right uu____1219
                                FStar_TypeChecker_Rel.resolve_implicits in
                            let solution =
                              FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1 None
                                (goal.context).FStar_TypeChecker_Env.range in
                            let implicits1 =
                              FStar_All.pipe_right
                                implicits.FStar_TypeChecker_Env.implicits
                                (FStar_List.filter
                                   (fun uu____1253  ->
                                      match uu____1253 with
                                      | (uu____1260,uu____1261,uu____1262,tm2,uu____1264,uu____1265)
                                          ->
                                          let uu____1266 =
                                            FStar_Syntax_Util.head_and_args
                                              tm2 in
                                          (match uu____1266 with
                                           | (hd1,uu____1277) ->
                                               let uu____1292 =
                                                 let uu____1293 =
                                                   FStar_Syntax_Subst.compress
                                                     hd1 in
                                                 uu____1293.FStar_Syntax_Syntax.n in
                                               (match uu____1292 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    uu____1296 -> true
                                                | uu____1305 -> false)))) in
                            (solve goal solution;
                             (let is_free_uvar uv t1 =
                                let free_uvars =
                                  let uu____1324 =
                                    let uu____1328 =
                                      FStar_Syntax_Free.uvars t1 in
                                    FStar_Util.set_elements uu____1328 in
                                  FStar_List.map FStar_Pervasives.fst
                                    uu____1324 in
                                FStar_List.existsML
                                  (fun u  -> FStar_Unionfind.equivalent u uv)
                                  free_uvars in
                              let appears uv goals =
                                FStar_List.existsML
                                  (fun g'  -> is_free_uvar uv g'.goal_ty)
                                  goals in
                              let checkone t1 goals =
                                let uu____1375 =
                                  FStar_Syntax_Util.head_and_args t1 in
                                match uu____1375 with
                                | (hd1,uu____1386) ->
                                    (match hd1.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (uv,uu____1402) -> appears uv goals
                                     | uu____1415 -> false) in
                              let sub_goals =
                                FStar_All.pipe_right implicits1
                                  (FStar_List.map
                                     (fun uu____1432  ->
                                        match uu____1432 with
                                        | (_msg,_env,_uvar,term,typ,uu____1444)
                                            ->
                                            let uu____1445 =
                                              bnorm goal.context term in
                                            let uu____1446 =
                                              bnorm goal.context typ in
                                            {
                                              context = (goal.context);
                                              witness = uu____1445;
                                              goal_ty = uu____1446
                                            })) in
                              let rec filter' f xs =
                                match xs with
                                | [] -> []
                                | x::xs1 ->
                                    let uu____1478 = f x xs1 in
                                    if uu____1478
                                    then
                                      let uu____1480 = filter' f xs1 in x ::
                                        uu____1480
                                    else filter' f xs1 in
                              let sub_goals1 =
                                filter'
                                  (fun g2  ->
                                     fun goals  ->
                                       let uu____1488 =
                                         checkone g2.witness goals in
                                       Prims.op_Negation uu____1488)
                                  sub_goals in
                              let uu____1489 =
                                add_implicits
                                  g1.FStar_TypeChecker_Env.implicits in
                              bind uu____1489
                                (fun uu____1491  ->
                                   bind dismiss
                                     (fun uu____1492  -> add_goals sub_goals1))))))))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1499 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1499 with
         | (tm1,t,guard) ->
             let uu____1507 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1507 with
              | (bs,comp) ->
                  let uu____1522 =
                    FStar_List.fold_left
                      (fun uu____1539  ->
                         fun uu____1540  ->
                           match (uu____1539, uu____1540) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1589 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1589 with
                                | (u,uu____1604,g_u) ->
                                    let uu____1612 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1612,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1522 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let uu____1644 =
                         let uu____1651 =
                           let uu____1657 =
                             FStar_Syntax_Util.comp_to_comp_typ comp1 in
                           uu____1657.FStar_Syntax_Syntax.effect_args in
                         match uu____1651 with
                         | pre::post::uu____1666 -> ((fst pre), (fst post))
                         | uu____1696 ->
                             failwith "apply_lemma: impossible: not a lemma" in
                       (match uu____1644 with
                        | (pre,post) ->
                            let uu____1719 =
                              let uu____1721 =
                                FStar_Syntax_Util.mk_squash post in
                              FStar_TypeChecker_Rel.try_teq false
                                goal.context uu____1721 goal.goal_ty in
                            (match uu____1719 with
                             | None  ->
                                 let uu____1723 =
                                   let uu____1724 =
                                     let uu____1725 =
                                       FStar_Syntax_Util.mk_squash post in
                                     FStar_Syntax_Print.term_to_string
                                       uu____1725 in
                                   let uu____1726 =
                                     FStar_Syntax_Print.term_to_string
                                       goal.goal_ty in
                                   FStar_Util.format2
                                     "apply_lemma: does not unify with goal: %s vs %s"
                                     uu____1724 uu____1726 in
                                 fail uu____1723
                             | Some g ->
                                 let g1 =
                                   let uu____1729 =
                                     FStar_TypeChecker_Rel.solve_deferred_constraints
                                       goal.context g in
                                   FStar_All.pipe_right uu____1729
                                     FStar_TypeChecker_Rel.resolve_implicits in
                                 let solution =
                                   FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                     None
                                     (goal.context).FStar_TypeChecker_Env.range in
                                 let implicits1 =
                                   FStar_All.pipe_right
                                     implicits.FStar_TypeChecker_Env.implicits
                                     (FStar_List.filter
                                        (fun uu____1763  ->
                                           match uu____1763 with
                                           | (uu____1770,uu____1771,uu____1772,tm2,uu____1774,uu____1775)
                                               ->
                                               let uu____1776 =
                                                 FStar_Syntax_Util.head_and_args
                                                   tm2 in
                                               (match uu____1776 with
                                                | (hd1,uu____1787) ->
                                                    let uu____1802 =
                                                      let uu____1803 =
                                                        FStar_Syntax_Subst.compress
                                                          hd1 in
                                                      uu____1803.FStar_Syntax_Syntax.n in
                                                    (match uu____1802 with
                                                     | FStar_Syntax_Syntax.Tm_uvar
                                                         uu____1806 -> true
                                                     | uu____1815 -> false)))) in
                                 (solve goal solution;
                                  (let is_free_uvar uv t1 =
                                     let free_uvars =
                                       let uu____1834 =
                                         let uu____1838 =
                                           FStar_Syntax_Free.uvars t1 in
                                         FStar_Util.set_elements uu____1838 in
                                       FStar_List.map FStar_Pervasives.fst
                                         uu____1834 in
                                     FStar_List.existsML
                                       (fun u  ->
                                          FStar_Unionfind.equivalent u uv)
                                       free_uvars in
                                   let appears uv goals =
                                     FStar_List.existsML
                                       (fun g'  -> is_free_uvar uv g'.goal_ty)
                                       goals in
                                   let checkone t1 goals =
                                     let uu____1885 =
                                       FStar_Syntax_Util.head_and_args t1 in
                                     match uu____1885 with
                                     | (hd1,uu____1896) ->
                                         (match hd1.FStar_Syntax_Syntax.n
                                          with
                                          | FStar_Syntax_Syntax.Tm_uvar
                                              (uv,uu____1912) ->
                                              appears uv goals
                                          | uu____1925 -> false) in
                                   let sub_goals =
                                     FStar_All.pipe_right implicits1
                                       (FStar_List.map
                                          (fun uu____1942  ->
                                             match uu____1942 with
                                             | (_msg,_env,_uvar,term,typ,uu____1954)
                                                 ->
                                                 let uu____1955 =
                                                   bnorm goal.context term in
                                                 let uu____1956 =
                                                   bnorm goal.context typ in
                                                 {
                                                   context = (goal.context);
                                                   witness = uu____1955;
                                                   goal_ty = uu____1956
                                                 })) in
                                   let rec filter' f xs =
                                     match xs with
                                     | [] -> []
                                     | x::xs1 ->
                                         let uu____1988 = f x xs1 in
                                         if uu____1988
                                         then
                                           let uu____1990 = filter' f xs1 in
                                           x :: uu____1990
                                         else filter' f xs1 in
                                   let sub_goals1 =
                                     filter'
                                       (fun g2  ->
                                          fun goals  ->
                                            let uu____1998 =
                                              checkone g2.witness goals in
                                            Prims.op_Negation uu____1998)
                                       sub_goals in
                                   let pregoal =
                                     mk_irrelevant goal.context pre in
                                   let sub_goals2 =
                                     let uu____2002 =
                                       istrivial goal.context pregoal.goal_ty in
                                     if uu____2002
                                     then sub_goals1
                                     else pregoal :: sub_goals1 in
                                   let uu____2005 =
                                     add_implicits
                                       g1.FStar_TypeChecker_Env.implicits in
                                   bind uu____2005
                                     (fun uu____2007  ->
                                        bind dismiss
                                          (fun uu____2008  ->
                                             add_goals sub_goals2)))))))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         try
           let uu____2018 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
           match uu____2018 with
           | (t1,typ,guard) ->
               let uu____2026 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                   goal.goal_ty in
               if uu____2026
               then (solve goal t1; dismiss)
               else
                 (let msg =
                    let uu____2031 = FStar_Syntax_Print.term_to_string t1 in
                    let uu____2032 =
                      let uu____2033 = bnorm goal.context typ in
                      FStar_Syntax_Print.term_to_string uu____2033 in
                    let uu____2034 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____2031
                      uu____2032 uu____2034 in
                  fail msg)
         with
         | e ->
             let uu____2038 =
               let uu____2039 = FStar_Syntax_Print.term_to_string t in
               let uu____2040 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.format2 "Term is not typeable: %s (%s)" uu____2039
                 uu____2040 in
             fail uu____2038)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2047 =
           FStar_All.pipe_left mlog
             (fun uu____2052  ->
                let uu____2053 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2054 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2053
                  uu____2054) in
         bind uu____2047
           (fun uu____2055  ->
              let uu____2056 =
                let uu____2058 =
                  let uu____2059 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2059 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2058 in
              match uu____2056 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2066::(x,uu____2068)::(e,uu____2070)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2104 =
                    let uu____2105 = FStar_Syntax_Subst.compress x in
                    uu____2105.FStar_Syntax_Syntax.n in
                  (match uu____2104 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___94_2111 = goal in
                         let uu____2112 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2115 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___94_2111.context);
                           witness = uu____2112;
                           goal_ty = uu____2115
                         } in
                       replace_cur goal1
                   | uu____2118 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2119 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2123 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2123 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2138 = FStar_Util.set_mem x fns_ty in
           if uu____2138
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2141 =
                FStar_TypeChecker_Util.new_implicit_var "clear"
                  (goal.goal_ty).FStar_Syntax_Syntax.pos env' goal.goal_ty in
              match uu____2141 with
              | (u,uu____2150,g) ->
                  let uu____2158 =
                    let uu____2159 =
                      FStar_TypeChecker_Rel.teq_nosmt goal.context
                        goal.witness u in
                    Prims.op_Negation uu____2159 in
                  if uu____2158
                  then fail "clear: unification failed"
                  else
                    (let new_goal =
                       let uu___95_2163 = goal in
                       let uu____2164 = bnorm env' u in
                       {
                         context = env';
                         witness = uu____2164;
                         goal_ty = (uu___95_2163.goal_ty)
                       } in
                     bind dismiss (fun uu____2165  -> add_goals [new_goal]))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2172 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2172 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2187 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2187 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2201 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2201 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___96_2224 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2231 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2231 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2243 =
                 let uu____2244 = FStar_Syntax_Print.bv_to_string x in
                 let uu____2245 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____2244 uu____2245 in
               fail uu____2243
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2258 = revert_all_hd xs1 in
        bind uu____2258 (fun uu____2260  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___97_2270 = g in
           {
             context = ctx';
             witness = (uu___97_2270.witness);
             goal_ty = (uu___97_2270.goal_ty)
           } in
         bind dismiss (fun uu____2271  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___98_2281 = g in
           {
             context = ctx';
             witness = (uu___98_2281.witness);
             goal_ty = (uu___98_2281.goal_ty)
           } in
         bind dismiss (fun uu____2282  -> add_goals [g']))
let rec bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2303 = FStar_Syntax_Subst.compress t in
          uu____2303.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2326 =
                let uu____2336 = ff hd1 in
                let uu____2337 =
                  FStar_List.map
                    (fun uu____2345  ->
                       match uu____2345 with
                       | (a,q) -> let uu____2352 = ff a in (uu____2352, q))
                    args in
                (uu____2336, uu____2337) in
              FStar_Syntax_Syntax.Tm_app uu____2326
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2381 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2381 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2387 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2387 t' in
                   let uu____2388 =
                     let uu____2403 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2403, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2388)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2422 -> tn in
        f env
          (let uu___99_2423 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___99_2423.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos = (uu___99_2423.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___99_2423.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2457 = f x in
      bind uu____2457
        (fun y  ->
           let uu____2461 = mapM f xs in
           bind uu____2461 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2493 = FStar_Syntax_Subst.compress t in
          uu____2493.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2519 = ff hd1 in
              bind uu____2519
                (fun hd2  ->
                   let fa uu____2530 =
                     match uu____2530 with
                     | (a,q) ->
                         let uu____2538 = ff a in
                         bind uu____2538 (fun a1  -> ret (a1, q)) in
                   let uu____2545 = mapM fa args in
                   bind uu____2545
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2589 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2589 with
               | (bs1,t') ->
                   let uu____2595 =
                     let uu____2597 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2597 t' in
                   bind uu____2595
                     (fun t''  ->
                        let uu____2599 =
                          let uu____2600 =
                            let uu____2615 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2615, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2600 in
                        ret uu____2599))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2634 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___100_2636 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___100_2636.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___100_2636.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___100_2636.FStar_Syntax_Syntax.vars)
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
                      (let g' =
                         let uu____2695 =
                           let uu____2696 =
                             FStar_TypeChecker_TcTerm.universe_of env typ in
                           FStar_Syntax_Util.mk_eq2 uu____2696 typ t1 ut in
                         mk_irrelevant env uu____2695 in
                       let uu____2697 = add_goals [g'] in
                       bind uu____2697
                         (fun uu____2699  ->
                            let uu____2700 =
                              bind tau
                                (fun uu____2702  ->
                                   let guard1 =
                                     let uu____2704 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env guard in
                                     FStar_All.pipe_right uu____2704
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env guard1;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.WHNF]
                                        env ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2700))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2715 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2715 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2736  ->
                   let uu____2737 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2737);
              bind dismiss_all
                (fun uu____2738  ->
                   let uu____2739 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2739
                     (fun gt'  ->
                        log ps
                          (fun uu____2743  ->
                             let uu____2744 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2744);
                        (let uu____2745 = push_goals gs in
                         bind uu____2745
                           (fun uu____2747  ->
                              add_goals
                                [(let uu___101_2748 = g in
                                  {
                                    context = (uu___101_2748.context);
                                    witness = (uu___101_2748.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2751 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2751 with
       | Some t ->
           let uu____2761 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2761 with
            | (hd1,args) ->
                let uu____2782 =
                  let uu____2790 =
                    let uu____2791 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2791.FStar_Syntax_Syntax.n in
                  (uu____2790, args) in
                (match uu____2782 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2801::(l,uu____2803)::(r,uu____2805)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.eq2_lid
                     ->
                     let uu____2839 =
                       let uu____2840 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____2840 in
                     if uu____2839
                     then
                       let uu____2842 =
                         let uu____2843 = FStar_Syntax_Print.term_to_string l in
                         let uu____2844 = FStar_Syntax_Print.term_to_string r in
                         FStar_Util.format2
                           "trefl: not a trivial equality (%s vs %s)"
                           uu____2843 uu____2844 in
                       fail uu____2842
                     else
                       (let t_unit1 = FStar_TypeChecker_Common.t_unit in
                        solve g t_unit1; dismiss)
                 | (hd2,uu____2851) ->
                     let uu____2862 =
                       let uu____2863 = FStar_Syntax_Print.term_to_string t in
                       FStar_Util.format1 "trefl: not an equality (%s)"
                         uu____2863 in
                     fail uu____2862))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___102_2873 = ps in
              {
                main_context = (uu___102_2873.main_context);
                main_goal = (uu___102_2873.main_goal);
                all_implicits = (uu___102_2873.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___102_2873.smt_goals)
              })
       | uu____2874 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___103_2882 = ps in
              {
                main_context = (uu___103_2882.main_context);
                main_goal = (uu___103_2882.main_goal);
                all_implicits = (uu___103_2882.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___103_2882.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2886 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2900 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2900 with
         | (t1,typ,guard) ->
             let uu____2910 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2910 with
              | (hd1,args) ->
                  let uu____2939 =
                    let uu____2947 =
                      let uu____2948 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2948.FStar_Syntax_Syntax.n in
                    (uu____2947, args) in
                  (match uu____2939 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2961)::(q,uu____2963)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___104_2992 = g in
                         let uu____2993 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2993;
                           witness = (uu___104_2992.witness);
                           goal_ty = (uu___104_2992.goal_ty)
                         } in
                       let g2 =
                         let uu___105_2995 = g in
                         let uu____2996 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2996;
                           witness = (uu___105_2995.witness);
                           goal_ty = (uu___105_2995.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____2999  ->
                            let uu____3000 = add_goals [g1; g2] in
                            bind uu____3000
                              (fun uu____3004  ->
                                 let uu____3005 =
                                   let uu____3008 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____3009 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____3008, uu____3009) in
                                 ret uu____3005))
                   | uu____3012 ->
                       let uu____3020 =
                         let uu____3021 =
                           FStar_Syntax_Print.term_to_string typ in
                         FStar_Util.format1 "Not a disjunction: %s"
                           uu____3021 in
                       fail uu____3020)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____3027 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____3031 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____3035 -> false
let order_binder:
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder -> order =
  fun x  ->
    fun y  ->
      let n1 = FStar_Syntax_Syntax.order_bv (fst x) (fst y) in
      if n1 < (Prims.parse_int "0")
      then Lt
      else if n1 = (Prims.parse_int "0") then Eq else Gt
let proofstate_of_goal_ty: env -> FStar_Syntax_Syntax.term -> proofstate =
  fun env  ->
    fun g  ->
      let g1 = let uu____3052 = bnorm env g in mk_irrelevant env uu____3052 in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = []
      }