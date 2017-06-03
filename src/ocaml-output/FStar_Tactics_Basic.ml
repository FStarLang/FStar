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
exception TacFailure of Prims.string
let uu___is_TacFailure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | TacFailure uu____151 -> true | uu____152 -> false
let __proj__TacFailure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | TacFailure uu____159 -> uu____159
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
      (let uu____406 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____406);
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
      let uu____446 = FStar_ST.read tac_verb_dbg in
      match uu____446 with
      | None  ->
          ((let uu____452 =
              let uu____454 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              Some uu____454 in
            FStar_ST.write tac_verb_dbg uu____452);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____480 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____480 then dump_proofstate ps "TACTING FAILING" else ());
       Failed (msg, ps))
let trytac t =
  mk_tac
    (fun ps  ->
       let tx = FStar_Syntax_Unionfind.new_transaction () in
       let uu____496 = run t ps in
       match uu____496 with
       | Success (a,q) ->
           (FStar_Syntax_Unionfind.commit tx; Success ((Some a), q))
       | Failed (uu____505,uu____506) ->
           (FStar_Syntax_Unionfind.rollback tx; Success (None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____515  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____522 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____522
      then ()
      else
        (let uu____524 =
           let uu____525 =
             let uu____526 = FStar_Syntax_Print.term_to_string solution in
             let uu____527 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____528 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____526
               uu____527 uu____528 in
           TacFailure uu____525 in
         raise uu____524)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____531 =
         let uu___78_532 = p in
         let uu____533 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_532.main_context);
           main_goal = (uu___78_532.main_goal);
           all_implicits = (uu___78_532.all_implicits);
           goals = uu____533;
           smt_goals = (uu___78_532.smt_goals)
         } in
       set uu____531)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_537 = p in
          {
            main_context = (uu___79_537.main_context);
            main_goal = (uu___79_537.main_goal);
            all_implicits = (uu___79_537.all_implicits);
            goals = [];
            smt_goals = (uu___79_537.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_546 = p in
            {
              main_context = (uu___80_546.main_context);
              main_goal = (uu___80_546.main_goal);
              all_implicits = (uu___80_546.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_546.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_555 = p in
            {
              main_context = (uu___81_555.main_context);
              main_goal = (uu___81_555.main_goal);
              all_implicits = (uu___81_555.all_implicits);
              goals = (uu___81_555.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_564 = p in
            {
              main_context = (uu___82_564.main_context);
              main_goal = (uu___82_564.main_goal);
              all_implicits = (uu___82_564.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___82_564.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_573 = p in
            {
              main_context = (uu___83_573.main_context);
              main_goal = (uu___83_573.main_goal);
              all_implicits = (uu___83_573.all_implicits);
              goals = (uu___83_573.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____579  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_586 = p in
            {
              main_context = (uu___84_586.main_context);
              main_goal = (uu___84_586.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_586.goals);
              smt_goals = (uu___84_586.smt_goals)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____596 = FStar_Syntax_Util.un_squash t in
    match uu____596 with
    | Some t' ->
        let uu____605 =
          let uu____606 = FStar_Syntax_Subst.compress t' in
          uu____606.FStar_Syntax_Syntax.n in
        (match uu____605 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____610 -> false)
    | uu____611 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____618 = FStar_Syntax_Util.un_squash t in
    match uu____618 with
    | Some t' ->
        let uu____627 =
          let uu____628 = FStar_Syntax_Subst.compress t' in
          uu____628.FStar_Syntax_Syntax.n in
        (match uu____627 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____632 -> false)
    | uu____633 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____645 = is_irrelevant g in
       if uu____645
       then bind dismiss (fun uu____647  -> add_smt_goals [g])
       else
         (let uu____649 =
            let uu____650 = FStar_Syntax_Print.term_to_string g.goal_ty in
            FStar_Util.format1
              "goal is not irrelevant: cannot dispatch to smt (%s)" uu____650 in
          fail uu____649))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____680 =
         try let uu____697 = FStar_List.splitAt n1 p.goals in ret uu____697
         with | uu____712 -> fail "divide: not enough goals" in
       bind uu____680
         (fun uu____723  ->
            match uu____723 with
            | (lgs,rgs) ->
                let lp =
                  let uu___85_738 = p in
                  {
                    main_context = (uu___85_738.main_context);
                    main_goal = (uu___85_738.main_goal);
                    all_implicits = (uu___85_738.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___86_740 = p in
                  {
                    main_context = (uu___86_740.main_context);
                    main_goal = (uu___86_740.main_goal);
                    all_implicits = (uu___86_740.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____741 = set lp in
                bind uu____741
                  (fun uu____745  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____752 = set rp in
                               bind uu____752
                                 (fun uu____756  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___87_764 = p in
                                                {
                                                  main_context =
                                                    (uu___87_764.main_context);
                                                  main_goal =
                                                    (uu___87_764.main_goal);
                                                  all_implicits =
                                                    (uu___87_764.all_implicits);
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
                                              let uu____765 = set p' in
                                              bind uu____765
                                                (fun uu____769  -> ret (a, b))))))))))
let focus_cur_goal f =
  let uu____782 = divide (Prims.parse_int "1") f idtac in
  bind uu____782 (fun uu____788  -> match uu____788 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____809::uu____810 ->
           let uu____812 =
             let uu____817 = map tau in
             divide (Prims.parse_int "1") tau uu____817 in
           bind uu____812
             (fun uu____825  -> match uu____825 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____848 =
        bind t1
          (fun uu____850  ->
             let uu____851 = map t2 in
             bind uu____851 (fun uu____855  -> ret ())) in
      focus_cur_goal uu____848
let arrow_one:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.comp) option
  =
  fun t  ->
    let uu____866 =
      let uu____867 = FStar_Syntax_Subst.compress t in
      uu____867.FStar_Syntax_Syntax.n in
    match uu____866 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) -> Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____928 =
          let uu____933 =
            let uu____934 = FStar_Syntax_Util.arrow bs c in
            FStar_Syntax_Syntax.mk_Total uu____934 in
          (b, uu____933) in
        Some uu____928
    | uu____941 -> None
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____950 = arrow_one goal.goal_ty in
       match uu____950 with
       | Some (b,c) ->
           let uu____961 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____961 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____981 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____984 =
                  let uu____985 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____985 in
                if uu____984
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____998 =
                     FStar_TypeChecker_Util.new_implicit_var "intro"
                       typ'.FStar_Syntax_Syntax.pos env' typ' in
                   match uu____998 with
                   | (u,uu____1009,g) ->
                       let uu____1017 =
                         let uu____1018 = FStar_Syntax_Util.abs [b1] u None in
                         FStar_TypeChecker_Rel.teq_nosmt goal.context
                           goal.witness uu____1018 in
                       if uu____1017
                       then
                         let uu____1031 =
                           let uu____1033 =
                             let uu___90_1034 = goal in
                             let uu____1035 = bnorm env' u in
                             let uu____1036 = bnorm env' typ' in
                             {
                               context = env';
                               witness = uu____1035;
                               goal_ty = uu____1036
                             } in
                           replace_cur uu____1033 in
                         bind uu____1031 (fun uu____1039  -> ret b1)
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
           let uu____1065 =
             let uu____1067 = FStar_List.map tr s in
             FStar_List.flatten uu____1067 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1065 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___91_1073 = goal in
            { context = (uu___91_1073.context); witness = w; goal_ty = t }))
let istrivial: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.UnfoldTac] in
      let t1 = FStar_TypeChecker_Normalize.normalize steps e t in
      let steps1 =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Simplify;
        FStar_TypeChecker_Normalize.UnfoldTac] in
      let t2 = FStar_TypeChecker_Normalize.normalize steps1 e t1 in
      is_true t2
let trivial: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____1088 = istrivial goal.context goal.goal_ty in
       if uu____1088
       then
         let t_unit1 = FStar_TypeChecker_Common.t_unit in
         (solve goal t_unit1; dismiss)
       else
         (let uu____1095 =
            let uu____1096 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            FStar_Util.format1 "Not a trivial goal: %s" uu____1096 in
          fail uu____1095))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1103 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1103 with
         | (tm1,t,guard) ->
             let uu____1111 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1111 with
              | (bs,comp) ->
                  let uu____1126 =
                    FStar_List.fold_left
                      (fun uu____1143  ->
                         fun uu____1144  ->
                           match (uu____1143, uu____1144) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1193 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1193 with
                                | (u,uu____1208,g_u) ->
                                    let uu____1216 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1216,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1126 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let ret_typ = comp_to_typ comp1 in
                       let uu____1249 =
                         FStar_TypeChecker_Rel.try_teq false goal.context
                           ret_typ goal.goal_ty in
                       (match uu____1249 with
                        | None  ->
                            let uu____1252 =
                              let uu____1253 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____1254 =
                                FStar_Syntax_Print.term_to_string ret_typ in
                              let uu____1255 =
                                FStar_Syntax_Print.term_to_string
                                  goal.goal_ty in
                              FStar_Util.format3
                                "apply: does not unify with goal: %s : %s vs %s"
                                uu____1253 uu____1254 uu____1255 in
                            fail uu____1252
                        | Some g ->
                            let g1 =
                              let uu____1258 =
                                FStar_TypeChecker_Rel.solve_deferred_constraints
                                  goal.context g in
                              FStar_All.pipe_right uu____1258
                                FStar_TypeChecker_Rel.resolve_implicits in
                            let solution =
                              FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1 None
                                (goal.context).FStar_TypeChecker_Env.range in
                            let implicits1 =
                              FStar_All.pipe_right
                                implicits.FStar_TypeChecker_Env.implicits
                                (FStar_List.filter
                                   (fun uu____1292  ->
                                      match uu____1292 with
                                      | (uu____1299,uu____1300,uu____1301,tm2,uu____1303,uu____1304)
                                          ->
                                          let uu____1305 =
                                            FStar_Syntax_Util.head_and_args
                                              tm2 in
                                          (match uu____1305 with
                                           | (hd1,uu____1316) ->
                                               let uu____1331 =
                                                 let uu____1332 =
                                                   FStar_Syntax_Subst.compress
                                                     hd1 in
                                                 uu____1332.FStar_Syntax_Syntax.n in
                                               (match uu____1331 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    uu____1335 -> true
                                                | uu____1344 -> false)))) in
                            (solve goal solution;
                             (let is_free_uvar uv t1 =
                                let free_uvars =
                                  let uu____1355 =
                                    let uu____1359 =
                                      FStar_Syntax_Free.uvars t1 in
                                    FStar_Util.set_elements uu____1359 in
                                  FStar_List.map FStar_Pervasives.fst
                                    uu____1355 in
                                FStar_List.existsML
                                  (fun u  ->
                                     FStar_Syntax_Unionfind.equiv u uv)
                                  free_uvars in
                              let appears uv goals =
                                FStar_List.existsML
                                  (fun g'  -> is_free_uvar uv g'.goal_ty)
                                  goals in
                              let checkone t1 goals =
                                let uu____1387 =
                                  FStar_Syntax_Util.head_and_args t1 in
                                match uu____1387 with
                                | (hd1,uu____1398) ->
                                    (match hd1.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (uv,uu____1414) -> appears uv goals
                                     | uu____1427 -> false) in
                              let sub_goals =
                                FStar_All.pipe_right implicits1
                                  (FStar_List.map
                                     (fun uu____1444  ->
                                        match uu____1444 with
                                        | (_msg,_env,_uvar,term,typ,uu____1456)
                                            ->
                                            let uu____1457 =
                                              bnorm goal.context term in
                                            let uu____1458 =
                                              bnorm goal.context typ in
                                            {
                                              context = (goal.context);
                                              witness = uu____1457;
                                              goal_ty = uu____1458
                                            })) in
                              let rec filter' f xs =
                                match xs with
                                | [] -> []
                                | x::xs1 ->
                                    let uu____1490 = f x xs1 in
                                    if uu____1490
                                    then
                                      let uu____1492 = filter' f xs1 in x ::
                                        uu____1492
                                    else filter' f xs1 in
                              let sub_goals1 =
                                filter'
                                  (fun g2  ->
                                     fun goals  ->
                                       let uu____1500 =
                                         checkone g2.witness goals in
                                       Prims.op_Negation uu____1500)
                                  sub_goals in
                              let uu____1501 =
                                add_implicits
                                  g1.FStar_TypeChecker_Env.implicits in
                              bind uu____1501
                                (fun uu____1503  ->
                                   bind dismiss
                                     (fun uu____1504  -> add_goals sub_goals1))))))))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1511 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1511 with
         | (tm1,t,guard) ->
             let uu____1519 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1519 with
              | (bs,comp) ->
                  let uu____1534 =
                    FStar_List.fold_left
                      (fun uu____1551  ->
                         fun uu____1552  ->
                           match (uu____1551, uu____1552) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1601 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1601 with
                                | (u,uu____1616,g_u) ->
                                    let uu____1624 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1624,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1534 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let uu____1656 =
                         let uu____1663 =
                           let uu____1669 =
                             FStar_Syntax_Util.comp_to_comp_typ comp1 in
                           uu____1669.FStar_Syntax_Syntax.effect_args in
                         match uu____1663 with
                         | pre::post::uu____1678 -> ((fst pre), (fst post))
                         | uu____1708 ->
                             failwith "apply_lemma: impossible: not a lemma" in
                       (match uu____1656 with
                        | (pre,post) ->
                            let uu____1731 =
                              let uu____1733 =
                                FStar_Syntax_Util.mk_squash post in
                              FStar_TypeChecker_Rel.try_teq false
                                goal.context uu____1733 goal.goal_ty in
                            (match uu____1731 with
                             | None  ->
                                 let uu____1735 =
                                   let uu____1736 =
                                     let uu____1737 =
                                       FStar_Syntax_Util.mk_squash post in
                                     FStar_Syntax_Print.term_to_string
                                       uu____1737 in
                                   let uu____1738 =
                                     FStar_Syntax_Print.term_to_string
                                       goal.goal_ty in
                                   FStar_Util.format2
                                     "apply_lemma: does not unify with goal: %s vs %s"
                                     uu____1736 uu____1738 in
                                 fail uu____1735
                             | Some g ->
                                 let g1 =
                                   let uu____1741 =
                                     FStar_TypeChecker_Rel.solve_deferred_constraints
                                       goal.context g in
                                   FStar_All.pipe_right uu____1741
                                     FStar_TypeChecker_Rel.resolve_implicits in
                                 let solution =
                                   FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                     None
                                     (goal.context).FStar_TypeChecker_Env.range in
                                 let implicits1 =
                                   FStar_All.pipe_right
                                     implicits.FStar_TypeChecker_Env.implicits
                                     (FStar_List.filter
                                        (fun uu____1775  ->
                                           match uu____1775 with
                                           | (uu____1782,uu____1783,uu____1784,tm2,uu____1786,uu____1787)
                                               ->
                                               let uu____1788 =
                                                 FStar_Syntax_Util.head_and_args
                                                   tm2 in
                                               (match uu____1788 with
                                                | (hd1,uu____1799) ->
                                                    let uu____1814 =
                                                      let uu____1815 =
                                                        FStar_Syntax_Subst.compress
                                                          hd1 in
                                                      uu____1815.FStar_Syntax_Syntax.n in
                                                    (match uu____1814 with
                                                     | FStar_Syntax_Syntax.Tm_uvar
                                                         uu____1818 -> true
                                                     | uu____1827 -> false)))) in
                                 (solve goal solution;
                                  (let is_free_uvar uv t1 =
                                     let free_uvars =
                                       let uu____1838 =
                                         let uu____1842 =
                                           FStar_Syntax_Free.uvars t1 in
                                         FStar_Util.set_elements uu____1842 in
                                       FStar_List.map FStar_Pervasives.fst
                                         uu____1838 in
                                     FStar_List.existsML
                                       (fun u  ->
                                          FStar_Syntax_Unionfind.equiv u uv)
                                       free_uvars in
                                   let appears uv goals =
                                     FStar_List.existsML
                                       (fun g'  -> is_free_uvar uv g'.goal_ty)
                                       goals in
                                   let checkone t1 goals =
                                     let uu____1870 =
                                       FStar_Syntax_Util.head_and_args t1 in
                                     match uu____1870 with
                                     | (hd1,uu____1881) ->
                                         (match hd1.FStar_Syntax_Syntax.n
                                          with
                                          | FStar_Syntax_Syntax.Tm_uvar
                                              (uv,uu____1897) ->
                                              appears uv goals
                                          | uu____1910 -> false) in
                                   let sub_goals =
                                     FStar_All.pipe_right implicits1
                                       (FStar_List.map
                                          (fun uu____1927  ->
                                             match uu____1927 with
                                             | (_msg,_env,_uvar,term,typ,uu____1939)
                                                 ->
                                                 let uu____1940 =
                                                   bnorm goal.context term in
                                                 let uu____1941 =
                                                   bnorm goal.context typ in
                                                 {
                                                   context = (goal.context);
                                                   witness = uu____1940;
                                                   goal_ty = uu____1941
                                                 })) in
                                   let rec filter' f xs =
                                     match xs with
                                     | [] -> []
                                     | x::xs1 ->
                                         let uu____1973 = f x xs1 in
                                         if uu____1973
                                         then
                                           let uu____1975 = filter' f xs1 in
                                           x :: uu____1975
                                         else filter' f xs1 in
                                   let sub_goals1 =
                                     filter'
                                       (fun g2  ->
                                          fun goals  ->
                                            let uu____1983 =
                                              checkone g2.witness goals in
                                            Prims.op_Negation uu____1983)
                                       sub_goals in
                                   let pregoal =
                                     mk_irrelevant goal.context pre in
                                   let sub_goals2 =
                                     let uu____1987 =
                                       istrivial goal.context pregoal.goal_ty in
                                     if uu____1987
                                     then sub_goals1
                                     else pregoal :: sub_goals1 in
                                   let uu____1990 =
                                     add_implicits
                                       g1.FStar_TypeChecker_Env.implicits in
                                   bind uu____1990
                                     (fun uu____1992  ->
                                        bind dismiss
                                          (fun uu____1993  ->
                                             add_goals sub_goals2)))))))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         try
           let uu____2003 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
           match uu____2003 with
           | (t1,typ,guard) ->
               let uu____2011 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                   goal.goal_ty in
               if uu____2011
               then (solve goal t1; dismiss)
               else
                 (let msg =
                    let uu____2016 = FStar_Syntax_Print.term_to_string t1 in
                    let uu____2017 =
                      let uu____2018 = bnorm goal.context typ in
                      FStar_Syntax_Print.term_to_string uu____2018 in
                    let uu____2019 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____2016
                      uu____2017 uu____2019 in
                  fail msg)
         with
         | e ->
             let uu____2023 =
               let uu____2024 = FStar_Syntax_Print.term_to_string t in
               let uu____2025 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.format2 "Term is not typeable: %s (%s)" uu____2024
                 uu____2025 in
             fail uu____2023)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2032 =
           FStar_All.pipe_left mlog
             (fun uu____2037  ->
                let uu____2038 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2039 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2038
                  uu____2039) in
         bind uu____2032
           (fun uu____2040  ->
              let uu____2041 =
                let uu____2043 =
                  let uu____2044 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2044 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2043 in
              match uu____2041 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2051::(x,uu____2053)::(e,uu____2055)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2089 =
                    let uu____2090 = FStar_Syntax_Subst.compress x in
                    uu____2090.FStar_Syntax_Syntax.n in
                  (match uu____2089 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___94_2096 = goal in
                         let uu____2097 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2100 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___94_2096.context);
                           witness = uu____2097;
                           goal_ty = uu____2100
                         } in
                       replace_cur goal1
                   | uu____2103 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2104 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2108 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2108 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2123 = FStar_Util.set_mem x fns_ty in
           if uu____2123
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2126 =
                FStar_TypeChecker_Util.new_implicit_var "clear"
                  (goal.goal_ty).FStar_Syntax_Syntax.pos env' goal.goal_ty in
              match uu____2126 with
              | (u,uu____2135,g) ->
                  let uu____2143 =
                    let uu____2144 =
                      FStar_TypeChecker_Rel.teq_nosmt goal.context
                        goal.witness u in
                    Prims.op_Negation uu____2144 in
                  if uu____2143
                  then fail "clear: unification failed"
                  else
                    (let new_goal =
                       let uu___95_2148 = goal in
                       let uu____2149 = bnorm env' u in
                       {
                         context = env';
                         witness = uu____2149;
                         goal_ty = (uu___95_2148.goal_ty)
                       } in
                     bind dismiss (fun uu____2150  -> add_goals [new_goal]))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2157 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2157 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2172 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2172 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2186 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2186 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___96_2209 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2216 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2216 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2228 =
                 let uu____2229 = FStar_Syntax_Print.bv_to_string x in
                 let uu____2230 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____2229 uu____2230 in
               fail uu____2228
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2243 = revert_all_hd xs1 in
        bind uu____2243 (fun uu____2245  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___97_2255 = g in
           {
             context = ctx';
             witness = (uu___97_2255.witness);
             goal_ty = (uu___97_2255.goal_ty)
           } in
         bind dismiss (fun uu____2256  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___98_2266 = g in
           {
             context = ctx';
             witness = (uu___98_2266.witness);
             goal_ty = (uu___98_2266.goal_ty)
           } in
         bind dismiss (fun uu____2267  -> add_goals [g']))
let rec bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2288 = FStar_Syntax_Subst.compress t in
          uu____2288.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2311 =
                let uu____2321 = ff hd1 in
                let uu____2322 =
                  FStar_List.map
                    (fun uu____2330  ->
                       match uu____2330 with
                       | (a,q) -> let uu____2337 = ff a in (uu____2337, q))
                    args in
                (uu____2321, uu____2322) in
              FStar_Syntax_Syntax.Tm_app uu____2311
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2366 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2366 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2372 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2372 t' in
                   let uu____2373 =
                     let uu____2388 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2388, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2373)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2407 -> tn in
        f env
          (let uu___99_2408 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___99_2408.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos = (uu___99_2408.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___99_2408.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2442 = f x in
      bind uu____2442
        (fun y  ->
           let uu____2446 = mapM f xs in
           bind uu____2446 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2478 = FStar_Syntax_Subst.compress t in
          uu____2478.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2504 = ff hd1 in
              bind uu____2504
                (fun hd2  ->
                   let fa uu____2515 =
                     match uu____2515 with
                     | (a,q) ->
                         let uu____2523 = ff a in
                         bind uu____2523 (fun a1  -> ret (a1, q)) in
                   let uu____2530 = mapM fa args in
                   bind uu____2530
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2574 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2574 with
               | (bs1,t') ->
                   let uu____2580 =
                     let uu____2582 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2582 t' in
                   bind uu____2580
                     (fun t''  ->
                        let uu____2584 =
                          let uu____2585 =
                            let uu____2600 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2600, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2585 in
                        ret uu____2584))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2619 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___100_2621 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___100_2621.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___100_2621.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___100_2621.FStar_Syntax_Syntax.vars)
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
          let uu____2642 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2642 with
          | (t1,lcomp,g) ->
              let uu____2650 =
                (let uu____2651 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2651) ||
                  (let uu____2652 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2652) in
              if uu____2650
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2658 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env typ in
                 match uu____2658 with
                 | (ut,uvs,guard) ->
                     (log ps
                        (fun uu____2676  ->
                           let uu____2677 =
                             FStar_Syntax_Print.term_to_string t1 in
                           let uu____2678 =
                             FStar_Syntax_Print.term_to_string ut in
                           FStar_Util.print2
                             "Pointwise_rec: making equality %s = %s\n"
                             uu____2677 uu____2678);
                      (let g' =
                         let uu____2680 =
                           let uu____2681 =
                             FStar_TypeChecker_TcTerm.universe_of env typ in
                           FStar_Syntax_Util.mk_eq2 uu____2681 typ t1 ut in
                         mk_irrelevant env uu____2680 in
                       let uu____2682 = add_goals [g'] in
                       bind uu____2682
                         (fun uu____2684  ->
                            let uu____2685 =
                              bind tau
                                (fun uu____2687  ->
                                   let guard1 =
                                     let uu____2689 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env guard in
                                     FStar_All.pipe_right uu____2689
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env guard1;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.WHNF]
                                        env ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2685))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2700 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2700 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2721  ->
                   let uu____2722 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2722);
              bind dismiss_all
                (fun uu____2723  ->
                   let uu____2724 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2724
                     (fun gt'  ->
                        log ps
                          (fun uu____2728  ->
                             let uu____2729 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2729);
                        (let uu____2730 = push_goals gs in
                         bind uu____2730
                           (fun uu____2732  ->
                              add_goals
                                [(let uu___101_2733 = g in
                                  {
                                    context = (uu___101_2733.context);
                                    witness = (uu___101_2733.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2736 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2736 with
       | Some t ->
           let uu____2746 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2746 with
            | (hd1,args) ->
                let uu____2767 =
                  let uu____2775 =
                    let uu____2776 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2776.FStar_Syntax_Syntax.n in
                  (uu____2775, args) in
                (match uu____2767 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2786::(l,uu____2788)::(r,uu____2790)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.eq2_lid
                     ->
                     let uu____2824 =
                       let uu____2825 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____2825 in
                     if uu____2824
                     then
                       let uu____2827 =
                         let uu____2828 = FStar_Syntax_Print.term_to_string l in
                         let uu____2829 = FStar_Syntax_Print.term_to_string r in
                         FStar_Util.format2
                           "trefl: not a trivial equality (%s vs %s)"
                           uu____2828 uu____2829 in
                       fail uu____2827
                     else
                       (let t_unit1 = FStar_TypeChecker_Common.t_unit in
                        solve g t_unit1; dismiss)
                 | (hd2,uu____2836) ->
                     let uu____2847 =
                       let uu____2848 = FStar_Syntax_Print.term_to_string t in
                       FStar_Util.format1 "trefl: not an equality (%s)"
                         uu____2848 in
                     fail uu____2847))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___102_2858 = ps in
              {
                main_context = (uu___102_2858.main_context);
                main_goal = (uu___102_2858.main_goal);
                all_implicits = (uu___102_2858.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___102_2858.smt_goals)
              })
       | uu____2859 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___103_2867 = ps in
              {
                main_context = (uu___103_2867.main_context);
                main_goal = (uu___103_2867.main_goal);
                all_implicits = (uu___103_2867.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___103_2867.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2871 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2885 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2885 with
         | (t1,typ,guard) ->
             let uu____2895 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2895 with
              | (hd1,args) ->
                  let uu____2924 =
                    let uu____2932 =
                      let uu____2933 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2933.FStar_Syntax_Syntax.n in
                    (uu____2932, args) in
                  (match uu____2924 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2946)::(q,uu____2948)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___104_2977 = g in
                         let uu____2978 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2978;
                           witness = (uu___104_2977.witness);
                           goal_ty = (uu___104_2977.goal_ty)
                         } in
                       let g2 =
                         let uu___105_2980 = g in
                         let uu____2981 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2981;
                           witness = (uu___105_2980.witness);
                           goal_ty = (uu___105_2980.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____2984  ->
                            let uu____2985 = add_goals [g1; g2] in
                            bind uu____2985
                              (fun uu____2989  ->
                                 let uu____2990 =
                                   let uu____2993 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____2994 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____2993, uu____2994) in
                                 ret uu____2990))
                   | uu____2997 ->
                       let uu____3005 =
                         let uu____3006 =
                           FStar_Syntax_Print.term_to_string typ in
                         FStar_Util.format1 "Not a disjunction: %s"
                           uu____3006 in
                       fail uu____3005)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____3012 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____3016 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____3020 -> false
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
      let uu____3040 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____3040 with
      | (u,uu____3048,g_u) ->
          let g = { context = env; witness = u; goal_ty = typ } in
          {
            main_context = env;
            main_goal = g;
            all_implicits = [];
            goals = [g];
            smt_goals = []
          }