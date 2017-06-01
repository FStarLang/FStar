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
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____384 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____387 = FStar_List.hd ps.goals in dump_goal ps uu____387))
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____397 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____397);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____403 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____403);
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
      let uu____440 = FStar_ST.read tac_verb_dbg in
      match uu____440 with
      | None  ->
          ((let uu____446 =
              let uu____448 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              Some uu____448 in
            FStar_ST.write tac_verb_dbg uu____446);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____474 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____474 then dump_proofstate ps "TACTING FAILING" else ());
       Failed (msg, ps))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____481  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____488 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____488
      then ()
      else
        (let uu____490 =
           let uu____491 =
             let uu____492 = FStar_Syntax_Print.term_to_string solution in
             let uu____493 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____494 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____492
               uu____493 uu____494 in
           Failure uu____491 in
         raise uu____490)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____497 =
         let uu___78_498 = p in
         let uu____499 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_498.main_context);
           main_goal = (uu___78_498.main_goal);
           all_implicits = (uu___78_498.all_implicits);
           goals = uu____499;
           smt_goals = (uu___78_498.smt_goals)
         } in
       set uu____497)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_503 = p in
          {
            main_context = (uu___79_503.main_context);
            main_goal = (uu___79_503.main_goal);
            all_implicits = (uu___79_503.all_implicits);
            goals = [];
            smt_goals = (uu___79_503.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_512 = p in
            {
              main_context = (uu___80_512.main_context);
              main_goal = (uu___80_512.main_goal);
              all_implicits = (uu___80_512.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_512.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_521 = p in
            {
              main_context = (uu___81_521.main_context);
              main_goal = (uu___81_521.main_goal);
              all_implicits = (uu___81_521.all_implicits);
              goals = (uu___81_521.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_530 = p in
            {
              main_context = (uu___82_530.main_context);
              main_goal = (uu___82_530.main_goal);
              all_implicits = (uu___82_530.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___82_530.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_539 = p in
            {
              main_context = (uu___83_539.main_context);
              main_goal = (uu___83_539.main_goal);
              all_implicits = (uu___83_539.all_implicits);
              goals = (uu___83_539.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____545  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_552 = p in
            {
              main_context = (uu___84_552.main_context);
              main_goal = (uu___84_552.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_552.goals);
              smt_goals = (uu___84_552.smt_goals)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____562 = FStar_Syntax_Util.un_squash t in
    match uu____562 with
    | Some t' ->
        let uu____571 =
          let uu____572 = FStar_Syntax_Subst.compress t' in
          uu____572.FStar_Syntax_Syntax.n in
        (match uu____571 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____576 -> false)
    | uu____577 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____584 = FStar_Syntax_Util.un_squash t in
    match uu____584 with
    | Some t' ->
        let uu____593 =
          let uu____594 = FStar_Syntax_Subst.compress t' in
          uu____594.FStar_Syntax_Syntax.n in
        (match uu____593 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____598 -> false)
    | uu____599 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____611 = is_irrelevant g in
       if uu____611
       then bind dismiss (fun uu____613  -> add_smt_goals [g])
       else
         (let uu____615 =
            let uu____616 = FStar_Syntax_Print.term_to_string g.goal_ty in
            FStar_Util.format1
              "goal is not irrelevant: cannot dispatch to smt (%s)" uu____616 in
          fail uu____615))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____646 =
         try let uu____663 = FStar_List.splitAt n1 p.goals in ret uu____663
         with | uu____678 -> fail "divide: not enough goals" in
       bind uu____646
         (fun uu____689  ->
            match uu____689 with
            | (lgs,rgs) ->
                let lp =
                  let uu___85_704 = p in
                  {
                    main_context = (uu___85_704.main_context);
                    main_goal = (uu___85_704.main_goal);
                    all_implicits = (uu___85_704.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___86_706 = p in
                  {
                    main_context = (uu___86_706.main_context);
                    main_goal = (uu___86_706.main_goal);
                    all_implicits = (uu___86_706.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____707 = set lp in
                bind uu____707
                  (fun uu____711  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____718 = set rp in
                               bind uu____718
                                 (fun uu____722  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___87_730 = p in
                                                {
                                                  main_context =
                                                    (uu___87_730.main_context);
                                                  main_goal =
                                                    (uu___87_730.main_goal);
                                                  all_implicits =
                                                    (uu___87_730.all_implicits);
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
                                              let uu____731 = set p' in
                                              bind uu____731
                                                (fun uu____735  -> ret (a, b))))))))))
let focus_cur_goal f =
  let uu____748 = divide (Prims.parse_int "1") f idtac in
  bind uu____748 (fun uu____754  -> match uu____754 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____775::uu____776 ->
           let uu____778 =
             let uu____783 = map tau in
             divide (Prims.parse_int "1") tau uu____783 in
           bind uu____778
             (fun uu____791  -> match uu____791 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____814 =
        bind t1
          (fun uu____816  ->
             let uu____817 = map t2 in
             bind uu____817 (fun uu____821  -> ret ())) in
      focus_cur_goal uu____814
let arrow_one:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.comp) option
  =
  fun t  ->
    let uu____832 =
      let uu____833 = FStar_Syntax_Subst.compress t in
      uu____833.FStar_Syntax_Syntax.n in
    match uu____832 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) -> Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____894 =
          let uu____899 =
            let uu____900 = FStar_Syntax_Util.arrow bs c in
            FStar_Syntax_Syntax.mk_Total uu____900 in
          (b, uu____899) in
        Some uu____894
    | uu____907 -> None
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____916 = arrow_one goal.goal_ty in
       match uu____916 with
       | Some (b,c) ->
           let uu____927 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____927 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____947 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____950 =
                  let uu____951 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____951 in
                if uu____950
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____964 =
                     FStar_TypeChecker_Util.new_implicit_var "intro"
                       typ'.FStar_Syntax_Syntax.pos env' typ' in
                   match uu____964 with
                   | (u,uu____975,g) ->
                       let uu____983 =
                         let uu____984 = FStar_Syntax_Util.abs [b1] u None in
                         FStar_TypeChecker_Rel.teq_nosmt goal.context
                           goal.witness uu____984 in
                       if uu____983
                       then
                         let uu____997 =
                           let uu____999 =
                             let uu___90_1000 = goal in
                             let uu____1001 = bnorm env' u in
                             let uu____1002 = bnorm env' typ' in
                             {
                               context = env';
                               witness = uu____1001;
                               goal_ty = uu____1002
                             } in
                           replace_cur uu____999 in
                         bind uu____997 (fun uu____1005  -> ret b1)
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
           let uu____1031 =
             let uu____1033 = FStar_List.map tr s in
             FStar_List.flatten uu____1033 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1031 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___91_1039 = goal in
            { context = (uu___91_1039.context); witness = w; goal_ty = t }))
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
       let uu____1051 = istrivial goal.context goal.goal_ty in
       if uu____1051
       then
         let t_unit1 = FStar_TypeChecker_Common.t_unit in
         (solve goal t_unit1; dismiss)
       else
         (let uu____1058 =
            let uu____1059 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            FStar_Util.format1 "Not a trivial goal: %s" uu____1059 in
          fail uu____1058))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1066 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1066 with
         | (tm1,t,guard) ->
             let uu____1074 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1074 with
              | (bs,comp) ->
                  let uu____1089 =
                    FStar_List.fold_left
                      (fun uu____1106  ->
                         fun uu____1107  ->
                           match (uu____1106, uu____1107) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1156 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1156 with
                                | (u,uu____1171,g_u) ->
                                    let uu____1179 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1179,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1089 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let ret_typ = comp_to_typ comp1 in
                       let uu____1212 =
                         FStar_TypeChecker_Rel.try_teq false goal.context
                           ret_typ goal.goal_ty in
                       (match uu____1212 with
                        | None  ->
                            let uu____1215 =
                              let uu____1216 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____1217 =
                                FStar_Syntax_Print.term_to_string ret_typ in
                              let uu____1218 =
                                FStar_Syntax_Print.term_to_string
                                  goal.goal_ty in
                              FStar_Util.format3
                                "apply: does not unify with goal: %s : %s vs %s"
                                uu____1216 uu____1217 uu____1218 in
                            fail uu____1215
                        | Some g ->
                            let g1 =
                              let uu____1221 =
                                FStar_TypeChecker_Rel.solve_deferred_constraints
                                  goal.context g in
                              FStar_All.pipe_right uu____1221
                                FStar_TypeChecker_Rel.resolve_implicits in
                            let solution =
                              FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1 None
                                (goal.context).FStar_TypeChecker_Env.range in
                            let implicits1 =
                              FStar_All.pipe_right
                                implicits.FStar_TypeChecker_Env.implicits
                                (FStar_List.filter
                                   (fun uu____1255  ->
                                      match uu____1255 with
                                      | (uu____1262,uu____1263,uu____1264,tm2,uu____1266,uu____1267)
                                          ->
                                          let uu____1268 =
                                            FStar_Syntax_Util.head_and_args
                                              tm2 in
                                          (match uu____1268 with
                                           | (hd1,uu____1279) ->
                                               let uu____1294 =
                                                 let uu____1295 =
                                                   FStar_Syntax_Subst.compress
                                                     hd1 in
                                                 uu____1295.FStar_Syntax_Syntax.n in
                                               (match uu____1294 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    uu____1298 -> true
                                                | uu____1307 -> false)))) in
                            (solve goal solution;
                             (let is_free_uvar uv t1 =
                                let free_uvars =
                                  let uu____1326 =
                                    let uu____1330 =
                                      FStar_Syntax_Free.uvars t1 in
                                    FStar_Util.set_elements uu____1330 in
                                  FStar_List.map FStar_Pervasives.fst
                                    uu____1326 in
                                FStar_List.existsML
                                  (fun u  -> FStar_Unionfind.equivalent u uv)
                                  free_uvars in
                              let appears uv goals =
                                FStar_List.existsML
                                  (fun g'  -> is_free_uvar uv g'.goal_ty)
                                  goals in
                              let checkone t1 goals =
                                let uu____1377 =
                                  FStar_Syntax_Util.head_and_args t1 in
                                match uu____1377 with
                                | (hd1,uu____1388) ->
                                    (match hd1.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (uv,uu____1404) -> appears uv goals
                                     | uu____1417 -> false) in
                              let sub_goals =
                                FStar_All.pipe_right implicits1
                                  (FStar_List.map
                                     (fun uu____1434  ->
                                        match uu____1434 with
                                        | (_msg,_env,_uvar,term,typ,uu____1446)
                                            ->
                                            let uu____1447 =
                                              bnorm goal.context term in
                                            let uu____1448 =
                                              bnorm goal.context typ in
                                            {
                                              context = (goal.context);
                                              witness = uu____1447;
                                              goal_ty = uu____1448
                                            })) in
                              let rec filter' f xs =
                                match xs with
                                | [] -> []
                                | x::xs1 ->
                                    let uu____1480 = f x xs1 in
                                    if uu____1480
                                    then
                                      let uu____1482 = filter' f xs1 in x ::
                                        uu____1482
                                    else filter' f xs1 in
                              let sub_goals1 =
                                filter'
                                  (fun g2  ->
                                     fun goals  ->
                                       let uu____1490 =
                                         checkone g2.witness goals in
                                       Prims.op_Negation uu____1490)
                                  sub_goals in
                              let uu____1491 =
                                add_implicits
                                  g1.FStar_TypeChecker_Env.implicits in
                              bind uu____1491
                                (fun uu____1493  ->
                                   bind dismiss
                                     (fun uu____1494  -> add_goals sub_goals1))))))))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1501 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1501 with
         | (tm1,t,guard) ->
             let uu____1509 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1509 with
              | (bs,comp) ->
                  let uu____1524 =
                    FStar_List.fold_left
                      (fun uu____1541  ->
                         fun uu____1542  ->
                           match (uu____1541, uu____1542) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1591 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1591 with
                                | (u,uu____1606,g_u) ->
                                    let uu____1614 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1614,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1524 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let uu____1646 =
                         let uu____1653 =
                           let uu____1659 =
                             FStar_Syntax_Util.comp_to_comp_typ comp1 in
                           uu____1659.FStar_Syntax_Syntax.effect_args in
                         match uu____1653 with
                         | pre::post::uu____1668 -> ((fst pre), (fst post))
                         | uu____1698 ->
                             failwith "apply_lemma: impossible: not a lemma" in
                       (match uu____1646 with
                        | (pre,post) ->
                            let uu____1721 =
                              let uu____1723 =
                                FStar_Syntax_Util.mk_squash post in
                              FStar_TypeChecker_Rel.try_teq false
                                goal.context uu____1723 goal.goal_ty in
                            (match uu____1721 with
                             | None  ->
                                 let uu____1725 =
                                   let uu____1726 =
                                     let uu____1727 =
                                       FStar_Syntax_Util.mk_squash post in
                                     FStar_Syntax_Print.term_to_string
                                       uu____1727 in
                                   let uu____1728 =
                                     FStar_Syntax_Print.term_to_string
                                       goal.goal_ty in
                                   FStar_Util.format2
                                     "apply_lemma: does not unify with goal: %s vs %s"
                                     uu____1726 uu____1728 in
                                 fail uu____1725
                             | Some g ->
                                 let g1 =
                                   let uu____1731 =
                                     FStar_TypeChecker_Rel.solve_deferred_constraints
                                       goal.context g in
                                   FStar_All.pipe_right uu____1731
                                     FStar_TypeChecker_Rel.resolve_implicits in
                                 let solution =
                                   FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                     None
                                     (goal.context).FStar_TypeChecker_Env.range in
                                 let implicits1 =
                                   FStar_All.pipe_right
                                     implicits.FStar_TypeChecker_Env.implicits
                                     (FStar_List.filter
                                        (fun uu____1765  ->
                                           match uu____1765 with
                                           | (uu____1772,uu____1773,uu____1774,tm2,uu____1776,uu____1777)
                                               ->
                                               let uu____1778 =
                                                 FStar_Syntax_Util.head_and_args
                                                   tm2 in
                                               (match uu____1778 with
                                                | (hd1,uu____1789) ->
                                                    let uu____1804 =
                                                      let uu____1805 =
                                                        FStar_Syntax_Subst.compress
                                                          hd1 in
                                                      uu____1805.FStar_Syntax_Syntax.n in
                                                    (match uu____1804 with
                                                     | FStar_Syntax_Syntax.Tm_uvar
                                                         uu____1808 -> true
                                                     | uu____1817 -> false)))) in
                                 (solve goal solution;
                                  (let is_free_uvar uv t1 =
                                     let free_uvars =
                                       let uu____1836 =
                                         let uu____1840 =
                                           FStar_Syntax_Free.uvars t1 in
                                         FStar_Util.set_elements uu____1840 in
                                       FStar_List.map FStar_Pervasives.fst
                                         uu____1836 in
                                     FStar_List.existsML
                                       (fun u  ->
                                          FStar_Unionfind.equivalent u uv)
                                       free_uvars in
                                   let appears uv goals =
                                     FStar_List.existsML
                                       (fun g'  -> is_free_uvar uv g'.goal_ty)
                                       goals in
                                   let checkone t1 goals =
                                     let uu____1887 =
                                       FStar_Syntax_Util.head_and_args t1 in
                                     match uu____1887 with
                                     | (hd1,uu____1898) ->
                                         (match hd1.FStar_Syntax_Syntax.n
                                          with
                                          | FStar_Syntax_Syntax.Tm_uvar
                                              (uv,uu____1914) ->
                                              appears uv goals
                                          | uu____1927 -> false) in
                                   let sub_goals =
                                     FStar_All.pipe_right implicits1
                                       (FStar_List.map
                                          (fun uu____1944  ->
                                             match uu____1944 with
                                             | (_msg,_env,_uvar,term,typ,uu____1956)
                                                 ->
                                                 let uu____1957 =
                                                   bnorm goal.context term in
                                                 let uu____1958 =
                                                   bnorm goal.context typ in
                                                 {
                                                   context = (goal.context);
                                                   witness = uu____1957;
                                                   goal_ty = uu____1958
                                                 })) in
                                   let rec filter' f xs =
                                     match xs with
                                     | [] -> []
                                     | x::xs1 ->
                                         let uu____1990 = f x xs1 in
                                         if uu____1990
                                         then
                                           let uu____1992 = filter' f xs1 in
                                           x :: uu____1992
                                         else filter' f xs1 in
                                   let sub_goals1 =
                                     filter'
                                       (fun g2  ->
                                          fun goals  ->
                                            let uu____2000 =
                                              checkone g2.witness goals in
                                            Prims.op_Negation uu____2000)
                                       sub_goals in
                                   let pregoal =
                                     mk_irrelevant goal.context pre in
                                   let sub_goals2 =
                                     let uu____2004 =
                                       istrivial goal.context pregoal.goal_ty in
                                     if uu____2004
                                     then sub_goals1
                                     else pregoal :: sub_goals1 in
                                   let uu____2007 =
                                     add_implicits
                                       g1.FStar_TypeChecker_Env.implicits in
                                   bind uu____2007
                                     (fun uu____2009  ->
                                        bind dismiss
                                          (fun uu____2010  ->
                                             add_goals sub_goals2)))))))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         try
           let uu____2020 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
           match uu____2020 with
           | (t1,typ,guard) ->
               let uu____2028 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                   goal.goal_ty in
               if uu____2028
               then (solve goal t1; dismiss)
               else
                 (let msg =
                    let uu____2033 = FStar_Syntax_Print.term_to_string t1 in
                    let uu____2034 =
                      let uu____2035 = bnorm goal.context typ in
                      FStar_Syntax_Print.term_to_string uu____2035 in
                    let uu____2036 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____2033
                      uu____2034 uu____2036 in
                  fail msg)
         with
         | e ->
             let uu____2040 =
               let uu____2041 = FStar_Syntax_Print.term_to_string t in
               let uu____2042 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.format2 "Term is not typeable: %s (%s)" uu____2041
                 uu____2042 in
             fail uu____2040)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2049 =
           FStar_All.pipe_left mlog
             (fun uu____2054  ->
                let uu____2055 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2056 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2055
                  uu____2056) in
         bind uu____2049
           (fun uu____2057  ->
              let uu____2058 =
                let uu____2060 =
                  let uu____2061 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2061 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2060 in
              match uu____2058 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2068::(x,uu____2070)::(e,uu____2072)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2106 =
                    let uu____2107 = FStar_Syntax_Subst.compress x in
                    uu____2107.FStar_Syntax_Syntax.n in
                  (match uu____2106 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___94_2113 = goal in
                         let uu____2114 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2117 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___94_2113.context);
                           witness = uu____2114;
                           goal_ty = uu____2117
                         } in
                       replace_cur goal1
                   | uu____2120 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2121 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2125 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2125 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2140 = FStar_Util.set_mem x fns_ty in
           if uu____2140
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2143 =
                FStar_TypeChecker_Util.new_implicit_var "clear"
                  (goal.goal_ty).FStar_Syntax_Syntax.pos env' goal.goal_ty in
              match uu____2143 with
              | (u,uu____2152,g) ->
                  let uu____2160 =
                    let uu____2161 =
                      FStar_TypeChecker_Rel.teq_nosmt goal.context
                        goal.witness u in
                    Prims.op_Negation uu____2161 in
                  if uu____2160
                  then fail "clear: unification failed"
                  else
                    (let new_goal =
                       let uu___95_2165 = goal in
                       let uu____2166 = bnorm env' u in
                       {
                         context = env';
                         witness = uu____2166;
                         goal_ty = (uu___95_2165.goal_ty)
                       } in
                     bind dismiss (fun uu____2167  -> add_goals [new_goal]))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2174 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2174 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2189 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2189 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2203 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2203 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___96_2226 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2233 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2233 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2245 =
                 let uu____2246 = FStar_Syntax_Print.bv_to_string x in
                 let uu____2247 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____2246 uu____2247 in
               fail uu____2245
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2260 = revert_all_hd xs1 in
        bind uu____2260 (fun uu____2262  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___97_2272 = g in
           {
             context = ctx';
             witness = (uu___97_2272.witness);
             goal_ty = (uu___97_2272.goal_ty)
           } in
         bind dismiss (fun uu____2273  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___98_2283 = g in
           {
             context = ctx';
             witness = (uu___98_2283.witness);
             goal_ty = (uu___98_2283.goal_ty)
           } in
         bind dismiss (fun uu____2284  -> add_goals [g']))
let rec bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2305 = FStar_Syntax_Subst.compress t in
          uu____2305.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2328 =
                let uu____2338 = ff hd1 in
                let uu____2339 =
                  FStar_List.map
                    (fun uu____2347  ->
                       match uu____2347 with
                       | (a,q) -> let uu____2354 = ff a in (uu____2354, q))
                    args in
                (uu____2338, uu____2339) in
              FStar_Syntax_Syntax.Tm_app uu____2328
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2383 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2383 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2389 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2389 t' in
                   let uu____2390 =
                     let uu____2405 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2405, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2390)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2424 -> tn in
        f env
          (let uu___99_2425 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___99_2425.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos = (uu___99_2425.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___99_2425.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2459 = f x in
      bind uu____2459
        (fun y  ->
           let uu____2463 = mapM f xs in
           bind uu____2463 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2495 = FStar_Syntax_Subst.compress t in
          uu____2495.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2521 = ff hd1 in
              bind uu____2521
                (fun hd2  ->
                   let fa uu____2532 =
                     match uu____2532 with
                     | (a,q) ->
                         let uu____2540 = ff a in
                         bind uu____2540 (fun a1  -> ret (a1, q)) in
                   let uu____2547 = mapM fa args in
                   bind uu____2547
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2591 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2591 with
               | (bs1,t') ->
                   let uu____2597 =
                     let uu____2599 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2599 t' in
                   bind uu____2597
                     (fun t''  ->
                        let uu____2601 =
                          let uu____2602 =
                            let uu____2617 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2617, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2602 in
                        ret uu____2601))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2636 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___100_2638 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___100_2638.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___100_2638.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___100_2638.FStar_Syntax_Syntax.vars)
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
          let uu____2659 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2659 with
          | (t1,lcomp,g) ->
              let uu____2667 =
                (let uu____2668 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2668) ||
                  (let uu____2669 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2669) in
              if uu____2667
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2675 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env typ in
                 match uu____2675 with
                 | (ut,uvs,guard) ->
                     (log ps
                        (fun uu____2693  ->
                           let uu____2694 =
                             FStar_Syntax_Print.term_to_string t1 in
                           let uu____2695 =
                             FStar_Syntax_Print.term_to_string ut in
                           FStar_Util.print2
                             "Pointwise_rec: making equality %s = %s\n"
                             uu____2694 uu____2695);
                      (let g' =
                         let uu____2697 =
                           let uu____2698 =
                             FStar_TypeChecker_TcTerm.universe_of env typ in
                           FStar_Syntax_Util.mk_eq2 uu____2698 typ t1 ut in
                         mk_irrelevant env uu____2697 in
                       let uu____2699 = add_goals [g'] in
                       bind uu____2699
                         (fun uu____2701  ->
                            let uu____2702 =
                              bind tau
                                (fun uu____2704  ->
                                   let guard1 =
                                     let uu____2706 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env guard in
                                     FStar_All.pipe_right uu____2706
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env guard1;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.WHNF]
                                        env ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2702))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2717 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2717 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2738  ->
                   let uu____2739 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2739);
              bind dismiss_all
                (fun uu____2740  ->
                   let uu____2741 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2741
                     (fun gt'  ->
                        log ps
                          (fun uu____2745  ->
                             let uu____2746 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2746);
                        (let uu____2747 = push_goals gs in
                         bind uu____2747
                           (fun uu____2749  ->
                              add_goals
                                [(let uu___101_2750 = g in
                                  {
                                    context = (uu___101_2750.context);
                                    witness = (uu___101_2750.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2753 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2753 with
       | Some t ->
           let uu____2763 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2763 with
            | (hd1,args) ->
                let uu____2784 =
                  let uu____2792 =
                    let uu____2793 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2793.FStar_Syntax_Syntax.n in
                  (uu____2792, args) in
                (match uu____2784 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2803::(l,uu____2805)::(r,uu____2807)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.eq2_lid
                     ->
                     let uu____2841 =
                       let uu____2842 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____2842 in
                     if uu____2841
                     then
                       let uu____2844 =
                         let uu____2845 = FStar_Syntax_Print.term_to_string l in
                         let uu____2846 = FStar_Syntax_Print.term_to_string r in
                         FStar_Util.format2
                           "trefl: not a trivial equality (%s vs %s)"
                           uu____2845 uu____2846 in
                       fail uu____2844
                     else
                       (let t_unit1 = FStar_TypeChecker_Common.t_unit in
                        solve g t_unit1; dismiss)
                 | (hd2,uu____2853) ->
                     let uu____2864 =
                       let uu____2865 = FStar_Syntax_Print.term_to_string t in
                       FStar_Util.format1 "trefl: not an equality (%s)"
                         uu____2865 in
                     fail uu____2864))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___102_2875 = ps in
              {
                main_context = (uu___102_2875.main_context);
                main_goal = (uu___102_2875.main_goal);
                all_implicits = (uu___102_2875.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___102_2875.smt_goals)
              })
       | uu____2876 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___103_2884 = ps in
              {
                main_context = (uu___103_2884.main_context);
                main_goal = (uu___103_2884.main_goal);
                all_implicits = (uu___103_2884.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___103_2884.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2888 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2902 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2902 with
         | (t1,typ,guard) ->
             let uu____2912 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2912 with
              | (hd1,args) ->
                  let uu____2941 =
                    let uu____2949 =
                      let uu____2950 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2950.FStar_Syntax_Syntax.n in
                    (uu____2949, args) in
                  (match uu____2941 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2963)::(q,uu____2965)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___104_2994 = g in
                         let uu____2995 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2995;
                           witness = (uu___104_2994.witness);
                           goal_ty = (uu___104_2994.goal_ty)
                         } in
                       let g2 =
                         let uu___105_2997 = g in
                         let uu____2998 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2998;
                           witness = (uu___105_2997.witness);
                           goal_ty = (uu___105_2997.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____3001  ->
                            let uu____3002 = add_goals [g1; g2] in
                            bind uu____3002
                              (fun uu____3006  ->
                                 let uu____3007 =
                                   let uu____3010 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____3011 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____3010, uu____3011) in
                                 ret uu____3007))
                   | uu____3014 ->
                       let uu____3022 =
                         let uu____3023 =
                           FStar_Syntax_Print.term_to_string typ in
                         FStar_Util.format1 "Not a disjunction: %s"
                           uu____3023 in
                       fail uu____3022)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____3029 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____3033 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____3037 -> false
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
      let g1 = let uu____3054 = bnorm env g in mk_irrelevant env uu____3054 in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = []
      }