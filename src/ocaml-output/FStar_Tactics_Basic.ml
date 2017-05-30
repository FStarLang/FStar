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
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____386 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____386);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____392 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____392);
      FStar_List.iter (dump_goal ps) ps.smt_goals
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let tac_verb_dbg: Prims.bool option FStar_ST.ref = FStar_Util.mk_ref None
let rec log: proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun ps  ->
    fun f  ->
      let uu____422 = FStar_ST.read tac_verb_dbg in
      match uu____422 with
      | None  ->
          ((let uu____428 =
              let uu____430 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              Some uu____430 in
            FStar_ST.write tac_verb_dbg uu____428);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____456 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____456 then dump_proofstate ps "TACTING FAILING" else ());
       Failed (msg, ps))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____463  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____470 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____470
      then ()
      else
        (let uu____472 =
           let uu____473 =
             let uu____474 = FStar_Syntax_Print.term_to_string solution in
             let uu____475 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____476 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____474
               uu____475 uu____476 in
           Failure uu____473 in
         raise uu____472)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____479 =
         let uu___78_480 = p in
         let uu____481 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_480.main_context);
           main_goal = (uu___78_480.main_goal);
           all_implicits = (uu___78_480.all_implicits);
           goals = uu____481;
           smt_goals = (uu___78_480.smt_goals)
         } in
       set uu____479)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_485 = p in
          {
            main_context = (uu___79_485.main_context);
            main_goal = (uu___79_485.main_goal);
            all_implicits = (uu___79_485.all_implicits);
            goals = [];
            smt_goals = (uu___79_485.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_494 = p in
            {
              main_context = (uu___80_494.main_context);
              main_goal = (uu___80_494.main_goal);
              all_implicits = (uu___80_494.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_494.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_503 = p in
            {
              main_context = (uu___81_503.main_context);
              main_goal = (uu___81_503.main_goal);
              all_implicits = (uu___81_503.all_implicits);
              goals = (uu___81_503.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_512 = p in
            {
              main_context = (uu___82_512.main_context);
              main_goal = (uu___82_512.main_goal);
              all_implicits = (uu___82_512.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___82_512.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_521 = p in
            {
              main_context = (uu___83_521.main_context);
              main_goal = (uu___83_521.main_goal);
              all_implicits = (uu___83_521.all_implicits);
              goals = (uu___83_521.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____527  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_534 = p in
            {
              main_context = (uu___84_534.main_context);
              main_goal = (uu___84_534.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_534.goals);
              smt_goals = (uu___84_534.smt_goals)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____544 = FStar_Syntax_Util.un_squash t in
    match uu____544 with
    | Some t' ->
        let uu____553 =
          let uu____554 = FStar_Syntax_Subst.compress t' in
          uu____554.FStar_Syntax_Syntax.n in
        (match uu____553 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____558 -> false)
    | uu____559 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____566 = FStar_Syntax_Util.un_squash t in
    match uu____566 with
    | Some t' ->
        let uu____575 =
          let uu____576 = FStar_Syntax_Subst.compress t' in
          uu____576.FStar_Syntax_Syntax.n in
        (match uu____575 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____580 -> false)
    | uu____581 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____593 = is_irrelevant g in
       if uu____593
       then bind dismiss (fun uu____595  -> add_smt_goals [g])
       else
         (let uu____597 =
            let uu____598 = FStar_Syntax_Print.term_to_string g.goal_ty in
            FStar_Util.format1
              "goal is not irrelevant: cannot dispatch to smt (%s)" uu____598 in
          fail uu____597))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____628 =
         try let uu____645 = FStar_List.splitAt n1 p.goals in ret uu____645
         with | uu____660 -> fail "diivde: not enough goals" in
       bind uu____628
         (fun uu____671  ->
            match uu____671 with
            | (lgs,rgs) ->
                let lp =
                  let uu___85_686 = p in
                  {
                    main_context = (uu___85_686.main_context);
                    main_goal = (uu___85_686.main_goal);
                    all_implicits = (uu___85_686.all_implicits);
                    goals = lgs;
                    smt_goals = (uu___85_686.smt_goals)
                  } in
                let rp =
                  let uu___86_688 = p in
                  {
                    main_context = (uu___86_688.main_context);
                    main_goal = (uu___86_688.main_goal);
                    all_implicits = (uu___86_688.all_implicits);
                    goals = rgs;
                    smt_goals = (uu___86_688.smt_goals)
                  } in
                let uu____689 = set lp in
                bind uu____689
                  (fun uu____693  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____700 = set rp in
                               bind uu____700
                                 (fun uu____704  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___87_712 = p in
                                                {
                                                  main_context =
                                                    (uu___87_712.main_context);
                                                  main_goal =
                                                    (uu___87_712.main_goal);
                                                  all_implicits =
                                                    (uu___87_712.all_implicits);
                                                  goals =
                                                    (FStar_List.append
                                                       lp'.goals rp'.goals);
                                                  smt_goals =
                                                    (uu___87_712.smt_goals)
                                                } in
                                              let uu____713 = set p' in
                                              bind uu____713
                                                (fun uu____717  -> ret (a, b))))))))))
let focus_cur_goal f =
  let uu____730 = divide (Prims.parse_int "1") f idtac in
  bind uu____730 (fun uu____736  -> match uu____736 with | (a,()) -> ret a)
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____759 = t1.tac_f p in
       match uu____759 with | Failed uu____762 -> t2.tac_f p | q -> q)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____783::uu____784 ->
           let uu____786 =
             let uu____791 = map tau in
             divide (Prims.parse_int "1") tau uu____791 in
           bind uu____786
             (fun uu____799  -> match uu____799 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____822 =
        bind t1
          (fun uu____824  ->
             let uu____825 = map t2 in
             bind uu____825 (fun uu____829  -> ret ())) in
      focus_cur_goal uu____822
let arrow_one:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.comp) option
  =
  fun t  ->
    let uu____840 =
      let uu____841 = FStar_Syntax_Subst.compress t in
      uu____841.FStar_Syntax_Syntax.n in
    match uu____840 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) -> Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____902 =
          let uu____907 =
            let uu____908 = FStar_Syntax_Util.arrow bs c in
            FStar_Syntax_Syntax.mk_Total uu____908 in
          (b, uu____907) in
        Some uu____902
    | uu____915 -> None
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____924 = arrow_one goal.goal_ty in
       match uu____924 with
       | Some (b,c) ->
           let uu____935 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____935 with
            | (b1::[],c1) ->
                let uu____952 =
                  let uu____953 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____953 in
                if uu____952
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____966 =
                     FStar_TypeChecker_Util.new_implicit_var "intro"
                       typ'.FStar_Syntax_Syntax.pos env' typ' in
                   match uu____966 with
                   | (u,uu____977,g) ->
                       let uu____985 =
                         let uu____986 = FStar_Syntax_Util.abs [b1] u None in
                         FStar_TypeChecker_Rel.teq_nosmt goal.context
                           goal.witness uu____986 in
                       if uu____985
                       then
                         let uu____999 =
                           let uu____1001 =
                             let uu___90_1002 = goal in
                             let uu____1003 =
                               FStar_TypeChecker_Normalize.unfold_whnf env'
                                 typ' in
                             {
                               context = env';
                               witness = u;
                               goal_ty = uu____1003
                             } in
                           replace_cur uu____1001 in
                         bind uu____999 (fun uu____1006  -> ret b1)
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
               [FStar_TypeChecker_Normalize.Primops] in
         let steps =
           let uu____1032 =
             let uu____1034 = FStar_List.map tr s in
             FStar_List.flatten uu____1034 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1032 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___91_1040 = goal in
            { context = (uu___91_1040.context); witness = w; goal_ty = t }))
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
       let uu____1052 = istrivial goal.context goal.goal_ty in
       if uu____1052
       then dismiss
       else
         (let uu____1055 =
            let uu____1056 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            FStar_Util.format1 "Not a trivial goal: %s" uu____1056 in
          fail uu____1055))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1063 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1063 with
         | (tm1,t,guard) ->
             let uu____1071 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1071 with
              | (bs,comp) ->
                  let uu____1086 =
                    FStar_List.fold_left
                      (fun uu____1103  ->
                         fun uu____1104  ->
                           match (uu____1103, uu____1104) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1153 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1153 with
                                | (u,uu____1168,g_u) ->
                                    let uu____1176 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1176,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1086 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let ret_typ = comp_to_typ comp1 in
                       let uu____1209 =
                         FStar_TypeChecker_Rel.try_teq false goal.context
                           ret_typ goal.goal_ty in
                       (match uu____1209 with
                        | None  ->
                            let uu____1212 =
                              let uu____1213 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____1214 =
                                FStar_Syntax_Print.term_to_string ret_typ in
                              let uu____1215 =
                                FStar_Syntax_Print.term_to_string
                                  goal.goal_ty in
                              FStar_Util.format3
                                "apply: does not unify with goal: %s : %s vs %s"
                                uu____1213 uu____1214 uu____1215 in
                            fail uu____1212
                        | Some g ->
                            let g1 =
                              let uu____1218 =
                                FStar_TypeChecker_Rel.solve_deferred_constraints
                                  goal.context g in
                              FStar_All.pipe_right uu____1218
                                FStar_TypeChecker_Rel.resolve_implicits in
                            let solution =
                              FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1 None
                                (goal.context).FStar_TypeChecker_Env.range in
                            let implicits1 =
                              FStar_All.pipe_right
                                implicits.FStar_TypeChecker_Env.implicits
                                (FStar_List.filter
                                   (fun uu____1252  ->
                                      match uu____1252 with
                                      | (uu____1259,uu____1260,uu____1261,tm2,uu____1263,uu____1264)
                                          ->
                                          let uu____1265 =
                                            FStar_Syntax_Util.head_and_args
                                              tm2 in
                                          (match uu____1265 with
                                           | (hd1,uu____1276) ->
                                               let uu____1291 =
                                                 let uu____1292 =
                                                   FStar_Syntax_Subst.compress
                                                     hd1 in
                                                 uu____1292.FStar_Syntax_Syntax.n in
                                               (match uu____1291 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    uu____1295 -> true
                                                | uu____1304 -> false)))) in
                            (solve goal solution;
                             (let is_free_uvar uv t1 =
                                let free_uvars =
                                  let uu____1323 =
                                    let uu____1327 =
                                      FStar_Syntax_Free.uvars t1 in
                                    FStar_Util.set_elements uu____1327 in
                                  FStar_List.map FStar_Pervasives.fst
                                    uu____1323 in
                                FStar_List.existsML
                                  (fun u  -> FStar_Unionfind.equivalent u uv)
                                  free_uvars in
                              let appears uv goals =
                                FStar_List.existsML
                                  (fun g'  -> is_free_uvar uv g'.goal_ty)
                                  goals in
                              let checkone t1 goals =
                                let uu____1374 =
                                  FStar_Syntax_Util.head_and_args t1 in
                                match uu____1374 with
                                | (hd1,uu____1385) ->
                                    (match hd1.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (uv,uu____1401) -> appears uv goals
                                     | uu____1414 -> false) in
                              let sub_goals =
                                FStar_All.pipe_right implicits1
                                  (FStar_List.map
                                     (fun uu____1431  ->
                                        match uu____1431 with
                                        | (_msg,_env,_uvar,term,typ,uu____1443)
                                            ->
                                            let uu____1444 =
                                              bnorm goal.context term in
                                            let uu____1445 =
                                              bnorm goal.context typ in
                                            {
                                              context = (goal.context);
                                              witness = uu____1444;
                                              goal_ty = uu____1445
                                            })) in
                              let rec filter' f xs =
                                match xs with
                                | [] -> []
                                | x::xs1 ->
                                    let uu____1477 = f x xs1 in
                                    if uu____1477
                                    then
                                      let uu____1479 = filter' f xs1 in x ::
                                        uu____1479
                                    else filter' f xs1 in
                              let sub_goals1 =
                                filter'
                                  (fun g2  ->
                                     fun goals  ->
                                       let uu____1487 =
                                         checkone g2.witness goals in
                                       Prims.op_Negation uu____1487)
                                  sub_goals in
                              let uu____1488 =
                                add_implicits
                                  g1.FStar_TypeChecker_Env.implicits in
                              bind uu____1488
                                (fun uu____1490  ->
                                   bind dismiss
                                     (fun uu____1491  -> add_goals sub_goals1))))))))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1498 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1498 with
         | (tm1,t,guard) ->
             let uu____1506 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1506 with
              | (bs,comp) ->
                  let uu____1521 =
                    FStar_List.fold_left
                      (fun uu____1538  ->
                         fun uu____1539  ->
                           match (uu____1538, uu____1539) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1588 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1588 with
                                | (u,uu____1603,g_u) ->
                                    let uu____1611 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1611,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1521 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let uu____1643 =
                         let uu____1650 =
                           let uu____1656 =
                             FStar_Syntax_Util.comp_to_comp_typ comp1 in
                           uu____1656.FStar_Syntax_Syntax.effect_args in
                         match uu____1650 with
                         | pre::post::uu____1665 -> ((fst pre), (fst post))
                         | uu____1695 ->
                             failwith "apply_lemma: impossible: not a lemma" in
                       (match uu____1643 with
                        | (pre,post) ->
                            let uu____1718 =
                              let uu____1720 =
                                FStar_Syntax_Util.mk_squash post in
                              FStar_TypeChecker_Rel.try_teq false
                                goal.context uu____1720 goal.goal_ty in
                            (match uu____1718 with
                             | None  ->
                                 let uu____1722 =
                                   let uu____1723 =
                                     let uu____1724 =
                                       FStar_Syntax_Util.mk_squash post in
                                     FStar_Syntax_Print.term_to_string
                                       uu____1724 in
                                   let uu____1725 =
                                     FStar_Syntax_Print.term_to_string
                                       goal.goal_ty in
                                   FStar_Util.format2
                                     "apply_lemma: does not unify with goal: %s vs %s"
                                     uu____1723 uu____1725 in
                                 fail uu____1722
                             | Some g ->
                                 let g1 =
                                   let uu____1728 =
                                     FStar_TypeChecker_Rel.solve_deferred_constraints
                                       goal.context g in
                                   FStar_All.pipe_right uu____1728
                                     FStar_TypeChecker_Rel.resolve_implicits in
                                 let solution =
                                   FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                     None
                                     (goal.context).FStar_TypeChecker_Env.range in
                                 let implicits1 =
                                   FStar_All.pipe_right
                                     implicits.FStar_TypeChecker_Env.implicits
                                     (FStar_List.filter
                                        (fun uu____1762  ->
                                           match uu____1762 with
                                           | (uu____1769,uu____1770,uu____1771,tm2,uu____1773,uu____1774)
                                               ->
                                               let uu____1775 =
                                                 FStar_Syntax_Util.head_and_args
                                                   tm2 in
                                               (match uu____1775 with
                                                | (hd1,uu____1786) ->
                                                    let uu____1801 =
                                                      let uu____1802 =
                                                        FStar_Syntax_Subst.compress
                                                          hd1 in
                                                      uu____1802.FStar_Syntax_Syntax.n in
                                                    (match uu____1801 with
                                                     | FStar_Syntax_Syntax.Tm_uvar
                                                         uu____1805 -> true
                                                     | uu____1814 -> false)))) in
                                 (solve goal solution;
                                  (let is_free_uvar uv t1 =
                                     let free_uvars =
                                       let uu____1833 =
                                         let uu____1837 =
                                           FStar_Syntax_Free.uvars t1 in
                                         FStar_Util.set_elements uu____1837 in
                                       FStar_List.map FStar_Pervasives.fst
                                         uu____1833 in
                                     FStar_List.existsML
                                       (fun u  ->
                                          FStar_Unionfind.equivalent u uv)
                                       free_uvars in
                                   let appears uv goals =
                                     FStar_List.existsML
                                       (fun g'  -> is_free_uvar uv g'.goal_ty)
                                       goals in
                                   let checkone t1 goals =
                                     let uu____1884 =
                                       FStar_Syntax_Util.head_and_args t1 in
                                     match uu____1884 with
                                     | (hd1,uu____1895) ->
                                         (match hd1.FStar_Syntax_Syntax.n
                                          with
                                          | FStar_Syntax_Syntax.Tm_uvar
                                              (uv,uu____1911) ->
                                              appears uv goals
                                          | uu____1924 -> false) in
                                   let sub_goals =
                                     FStar_All.pipe_right implicits1
                                       (FStar_List.map
                                          (fun uu____1941  ->
                                             match uu____1941 with
                                             | (_msg,_env,_uvar,term,typ,uu____1953)
                                                 ->
                                                 let uu____1954 =
                                                   bnorm goal.context term in
                                                 let uu____1955 =
                                                   bnorm goal.context typ in
                                                 {
                                                   context = (goal.context);
                                                   witness = uu____1954;
                                                   goal_ty = uu____1955
                                                 })) in
                                   let rec filter' f xs =
                                     match xs with
                                     | [] -> []
                                     | x::xs1 ->
                                         let uu____1987 = f x xs1 in
                                         if uu____1987
                                         then
                                           let uu____1989 = filter' f xs1 in
                                           x :: uu____1989
                                         else filter' f xs1 in
                                   let sub_goals1 =
                                     filter'
                                       (fun g2  ->
                                          fun goals  ->
                                            let uu____1997 =
                                              checkone g2.witness goals in
                                            Prims.op_Negation uu____1997)
                                       sub_goals in
                                   let pregoal =
                                     mk_irrelevant goal.context pre in
                                   let sub_goals2 =
                                     let uu____2001 =
                                       istrivial goal.context pregoal.goal_ty in
                                     if uu____2001
                                     then sub_goals1
                                     else pregoal :: sub_goals1 in
                                   let uu____2004 =
                                     add_implicits
                                       g1.FStar_TypeChecker_Env.implicits in
                                   bind uu____2004
                                     (fun uu____2006  ->
                                        bind dismiss
                                          (fun uu____2007  ->
                                             add_goals sub_goals2)))))))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         try
           let uu____2017 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
           match uu____2017 with
           | (t1,typ,guard) ->
               let uu____2025 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                   goal.goal_ty in
               if uu____2025
               then (solve goal t1; dismiss)
               else
                 (let msg =
                    let uu____2030 = FStar_Syntax_Print.term_to_string t1 in
                    let uu____2031 =
                      let uu____2032 = bnorm goal.context typ in
                      FStar_Syntax_Print.term_to_string uu____2032 in
                    let uu____2033 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____2030
                      uu____2031 uu____2033 in
                  fail msg)
         with
         | e ->
             let uu____2037 =
               let uu____2038 = FStar_Syntax_Print.term_to_string t in
               let uu____2039 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.format2 "Term is not typeable: %s (%s)" uu____2038
                 uu____2039 in
             fail uu____2037)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2046 =
           FStar_All.pipe_left mlog
             (fun uu____2051  ->
                let uu____2052 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2053 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2052
                  uu____2053) in
         bind uu____2046
           (fun uu____2054  ->
              let uu____2055 =
                let uu____2057 =
                  let uu____2058 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2058 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2057 in
              match uu____2055 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2065::(x,uu____2067)::(e,uu____2069)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2103 =
                    let uu____2104 = FStar_Syntax_Subst.compress x in
                    uu____2104.FStar_Syntax_Syntax.n in
                  (match uu____2103 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___94_2110 = goal in
                         let uu____2111 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___94_2110.context);
                           witness = (uu___94_2110.witness);
                           goal_ty = uu____2111
                         } in
                       replace_cur goal1
                   | uu____2114 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2115 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2119 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2119 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____2132 = FStar_Util.set_mem x fns in
           if uu____2132
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___95_2136 = goal in
                {
                  context = env';
                  witness = (uu___95_2136.witness);
                  goal_ty = (uu___95_2136.goal_ty)
                } in
              bind dismiss (fun uu____2137  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2144 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2144 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2159 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2159 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2173 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2173 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___96_2196 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2203 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2203 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2215 =
                 let uu____2216 = FStar_Syntax_Print.bv_to_string x in
                 let uu____2217 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____2216 uu____2217 in
               fail uu____2215
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2230 = revert_all_hd xs1 in
        bind uu____2230 (fun uu____2232  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___97_2242 = g in
           {
             context = ctx';
             witness = (uu___97_2242.witness);
             goal_ty = (uu___97_2242.goal_ty)
           } in
         bind dismiss (fun uu____2243  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___98_2253 = g in
           {
             context = ctx';
             witness = (uu___98_2253.witness);
             goal_ty = (uu___98_2253.goal_ty)
           } in
         bind dismiss (fun uu____2254  -> add_goals [g']))
let rec bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2275 = FStar_Syntax_Subst.compress t in
          uu____2275.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2298 =
                let uu____2308 = ff hd1 in
                let uu____2309 =
                  FStar_List.map
                    (fun uu____2317  ->
                       match uu____2317 with
                       | (a,q) -> let uu____2324 = ff a in (uu____2324, q))
                    args in
                (uu____2308, uu____2309) in
              FStar_Syntax_Syntax.Tm_app uu____2298
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2353 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2353 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2359 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2359 t' in
                   let uu____2360 =
                     let uu____2375 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2375, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2360)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2394 -> tn in
        f env
          (let uu___99_2395 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___99_2395.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos = (uu___99_2395.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___99_2395.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2429 = f x in
      bind uu____2429
        (fun y  ->
           let uu____2433 = mapM f xs in
           bind uu____2433 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2465 = FStar_Syntax_Subst.compress t in
          uu____2465.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2491 = ff hd1 in
              bind uu____2491
                (fun hd2  ->
                   let fa uu____2502 =
                     match uu____2502 with
                     | (a,q) ->
                         let uu____2510 = ff a in
                         bind uu____2510 (fun a1  -> ret (a1, q)) in
                   let uu____2517 = mapM fa args in
                   bind uu____2517
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2561 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2561 with
               | (bs1,t') ->
                   let uu____2567 =
                     let uu____2569 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2569 t' in
                   bind uu____2567
                     (fun t''  ->
                        let uu____2571 =
                          let uu____2572 =
                            let uu____2587 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2587, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2572 in
                        ret uu____2571))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2606 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___100_2608 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___100_2608.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___100_2608.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___100_2608.FStar_Syntax_Syntax.vars)
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
          let uu____2629 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2629 with
          | (t1,lcomp,g) ->
              let uu____2637 =
                (let uu____2638 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2638) ||
                  (let uu____2639 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2639) in
              if uu____2637
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2645 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env typ in
                 match uu____2645 with
                 | (ut,uvs,guard) ->
                     (log ps
                        (fun uu____2663  ->
                           let uu____2664 =
                             FStar_Syntax_Print.term_to_string t1 in
                           let uu____2665 =
                             FStar_Syntax_Print.term_to_string ut in
                           FStar_Util.print2
                             "Pointwise_rec: making equality %s = %s\n"
                             uu____2664 uu____2665);
                      (let g' =
                         let uu____2667 =
                           let uu____2668 =
                             FStar_TypeChecker_TcTerm.universe_of env typ in
                           FStar_Syntax_Util.mk_eq2 uu____2668 typ t1 ut in
                         mk_irrelevant env uu____2667 in
                       let uu____2669 = add_goals [g'] in
                       bind uu____2669
                         (fun uu____2671  ->
                            let uu____2672 =
                              bind tau
                                (fun uu____2674  ->
                                   let guard1 =
                                     let uu____2676 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env guard in
                                     FStar_All.pipe_right uu____2676
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env guard1;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.WHNF]
                                        env ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2672))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2687 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2687 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2708  ->
                   let uu____2709 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2709);
              bind dismiss_all
                (fun uu____2710  ->
                   let uu____2711 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2711
                     (fun gt'  ->
                        log ps
                          (fun uu____2715  ->
                             let uu____2716 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2716);
                        (let uu____2717 = push_goals gs in
                         bind uu____2717
                           (fun uu____2719  ->
                              add_goals
                                [(let uu___101_2720 = g in
                                  {
                                    context = (uu___101_2720.context);
                                    witness = (uu___101_2720.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2723 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2723 with
       | Some t ->
           let uu____2733 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2733 with
            | (hd1,args) ->
                let uu____2754 =
                  let uu____2762 =
                    let uu____2763 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2763.FStar_Syntax_Syntax.n in
                  (uu____2762, args) in
                (match uu____2754 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2773::(l,uu____2775)::(r,uu____2777)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.eq2_lid
                     ->
                     let uu____2811 =
                       FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                     if uu____2811
                     then dismiss
                     else fail "trefl: not a trivial equality"
                 | (hd2,uu____2815) ->
                     let uu____2826 =
                       let uu____2827 =
                         FStar_Syntax_Print.term_to_string
                           (let uu___102_2828 = g.goal_ty in
                            {
                              FStar_Syntax_Syntax.n = hd2;
                              FStar_Syntax_Syntax.tk =
                                (uu___102_2828.FStar_Syntax_Syntax.tk);
                              FStar_Syntax_Syntax.pos =
                                (uu___102_2828.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___102_2828.FStar_Syntax_Syntax.vars)
                            }) in
                       FStar_Util.format1 "trefl: not an equality (%s)"
                         uu____2827 in
                     fail uu____2826))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___103_2842 = ps in
              {
                main_context = (uu___103_2842.main_context);
                main_goal = (uu___103_2842.main_goal);
                all_implicits = (uu___103_2842.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___103_2842.smt_goals)
              })
       | uu____2843 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___104_2851 = ps in
              {
                main_context = (uu___104_2851.main_context);
                main_goal = (uu___104_2851.main_goal);
                all_implicits = (uu___104_2851.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___104_2851.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2855 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2869 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2869 with
         | (t1,typ,guard) ->
             let uu____2879 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2879 with
              | (hd1,args) ->
                  let uu____2908 =
                    let uu____2916 =
                      let uu____2917 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2917.FStar_Syntax_Syntax.n in
                    (uu____2916, args) in
                  (match uu____2908 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2930)::(q,uu____2932)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___105_2961 = g in
                         let uu____2962 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2962;
                           witness = (uu___105_2961.witness);
                           goal_ty = (uu___105_2961.goal_ty)
                         } in
                       let g2 =
                         let uu___106_2964 = g in
                         let uu____2965 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2965;
                           witness = (uu___106_2964.witness);
                           goal_ty = (uu___106_2964.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____2968  ->
                            let uu____2969 = add_goals [g1; g2] in
                            bind uu____2969
                              (fun uu____2973  ->
                                 let uu____2974 =
                                   let uu____2977 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____2978 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____2977, uu____2978) in
                                 ret uu____2974))
                   | uu____2981 ->
                       let uu____2989 =
                         let uu____2990 =
                           FStar_Syntax_Print.term_to_string typ in
                         FStar_Util.format1 "Not a disjunction: %s"
                           uu____2990 in
                       fail uu____2989)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2996 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____3000 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____3004 -> false
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
      let g1 = let uu____3021 = bnorm env g in mk_irrelevant env uu____3021 in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = []
      }