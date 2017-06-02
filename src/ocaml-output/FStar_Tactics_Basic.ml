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
let trytac t =
  mk_tac
    (fun ps  ->
       let tx = FStar_Syntax_Unionfind.new_transaction () in
       let uu____490 = run t ps in
       match uu____490 with
       | Success (a,q) ->
           (FStar_Syntax_Unionfind.commit tx; Success ((Some a), q))
       | Failed (uu____499,uu____500) ->
           (FStar_Syntax_Unionfind.rollback tx; Success (None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____509  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____516 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____516
      then ()
      else
        (let uu____518 =
           let uu____519 =
             let uu____520 = FStar_Syntax_Print.term_to_string solution in
             let uu____521 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____522 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____520
               uu____521 uu____522 in
           Failure uu____519 in
         raise uu____518)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____525 =
         let uu___78_526 = p in
         let uu____527 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_526.main_context);
           main_goal = (uu___78_526.main_goal);
           all_implicits = (uu___78_526.all_implicits);
           goals = uu____527;
           smt_goals = (uu___78_526.smt_goals)
         } in
       set uu____525)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_531 = p in
          {
            main_context = (uu___79_531.main_context);
            main_goal = (uu___79_531.main_goal);
            all_implicits = (uu___79_531.all_implicits);
            goals = [];
            smt_goals = (uu___79_531.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_540 = p in
            {
              main_context = (uu___80_540.main_context);
              main_goal = (uu___80_540.main_goal);
              all_implicits = (uu___80_540.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_540.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_549 = p in
            {
              main_context = (uu___81_549.main_context);
              main_goal = (uu___81_549.main_goal);
              all_implicits = (uu___81_549.all_implicits);
              goals = (uu___81_549.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_558 = p in
            {
              main_context = (uu___82_558.main_context);
              main_goal = (uu___82_558.main_goal);
              all_implicits = (uu___82_558.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___82_558.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_567 = p in
            {
              main_context = (uu___83_567.main_context);
              main_goal = (uu___83_567.main_goal);
              all_implicits = (uu___83_567.all_implicits);
              goals = (uu___83_567.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____573  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_580 = p in
            {
              main_context = (uu___84_580.main_context);
              main_goal = (uu___84_580.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_580.goals);
              smt_goals = (uu___84_580.smt_goals)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____590 = FStar_Syntax_Util.un_squash t in
    match uu____590 with
    | Some t' ->
        let uu____599 =
          let uu____600 = FStar_Syntax_Subst.compress t' in
          uu____600.FStar_Syntax_Syntax.n in
        (match uu____599 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____604 -> false)
    | uu____605 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____612 = FStar_Syntax_Util.un_squash t in
    match uu____612 with
    | Some t' ->
        let uu____621 =
          let uu____622 = FStar_Syntax_Subst.compress t' in
          uu____622.FStar_Syntax_Syntax.n in
        (match uu____621 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____626 -> false)
    | uu____627 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____639 = is_irrelevant g in
       if uu____639
       then bind dismiss (fun uu____641  -> add_smt_goals [g])
       else
         (let uu____643 =
            let uu____644 = FStar_Syntax_Print.term_to_string g.goal_ty in
            FStar_Util.format1
              "goal is not irrelevant: cannot dispatch to smt (%s)" uu____644 in
          fail uu____643))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____674 =
         try let uu____691 = FStar_List.splitAt n1 p.goals in ret uu____691
         with | uu____706 -> fail "divide: not enough goals" in
       bind uu____674
         (fun uu____717  ->
            match uu____717 with
            | (lgs,rgs) ->
                let lp =
                  let uu___85_732 = p in
                  {
                    main_context = (uu___85_732.main_context);
                    main_goal = (uu___85_732.main_goal);
                    all_implicits = (uu___85_732.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___86_734 = p in
                  {
                    main_context = (uu___86_734.main_context);
                    main_goal = (uu___86_734.main_goal);
                    all_implicits = (uu___86_734.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____735 = set lp in
                bind uu____735
                  (fun uu____739  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____746 = set rp in
                               bind uu____746
                                 (fun uu____750  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___87_758 = p in
                                                {
                                                  main_context =
                                                    (uu___87_758.main_context);
                                                  main_goal =
                                                    (uu___87_758.main_goal);
                                                  all_implicits =
                                                    (uu___87_758.all_implicits);
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
                                              let uu____759 = set p' in
                                              bind uu____759
                                                (fun uu____763  -> ret (a, b))))))))))
let focus_cur_goal f =
  let uu____776 = divide (Prims.parse_int "1") f idtac in
  bind uu____776 (fun uu____782  -> match uu____782 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____803::uu____804 ->
           let uu____806 =
             let uu____811 = map tau in
             divide (Prims.parse_int "1") tau uu____811 in
           bind uu____806
             (fun uu____819  -> match uu____819 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____842 =
        bind t1
          (fun uu____844  ->
             let uu____845 = map t2 in
             bind uu____845 (fun uu____849  -> ret ())) in
      focus_cur_goal uu____842
let arrow_one:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.comp) option
  =
  fun t  ->
    let uu____860 =
      let uu____861 = FStar_Syntax_Subst.compress t in
      uu____861.FStar_Syntax_Syntax.n in
    match uu____860 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) -> Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____922 =
          let uu____927 =
            let uu____928 = FStar_Syntax_Util.arrow bs c in
            FStar_Syntax_Syntax.mk_Total uu____928 in
          (b, uu____927) in
        Some uu____922
    | uu____935 -> None
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____944 = arrow_one goal.goal_ty in
       match uu____944 with
       | Some (b,c) ->
           let uu____955 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____955 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____975 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____978 =
                  let uu____979 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____979 in
                if uu____978
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____992 =
                     FStar_TypeChecker_Util.new_implicit_var "intro"
                       typ'.FStar_Syntax_Syntax.pos env' typ' in
                   match uu____992 with
                   | (u,uu____1003,g) ->
                       let uu____1011 =
                         let uu____1012 = FStar_Syntax_Util.abs [b1] u None in
                         FStar_TypeChecker_Rel.teq_nosmt goal.context
                           goal.witness uu____1012 in
                       if uu____1011
                       then
                         let uu____1025 =
                           let uu____1027 =
                             let uu___90_1028 = goal in
                             let uu____1029 = bnorm env' u in
                             let uu____1030 = bnorm env' typ' in
                             {
                               context = env';
                               witness = uu____1029;
                               goal_ty = uu____1030
                             } in
                           replace_cur uu____1027 in
                         bind uu____1025 (fun uu____1033  -> ret b1)
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
           let uu____1059 =
             let uu____1061 = FStar_List.map tr s in
             FStar_List.flatten uu____1061 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1059 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___91_1067 = goal in
            { context = (uu___91_1067.context); witness = w; goal_ty = t }))
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
       let uu____1079 = istrivial goal.context goal.goal_ty in
       if uu____1079
       then
         let t_unit1 = FStar_TypeChecker_Common.t_unit in
         (solve goal t_unit1; dismiss)
       else
         (let uu____1086 =
            let uu____1087 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            FStar_Util.format1 "Not a trivial goal: %s" uu____1087 in
          fail uu____1086))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1094 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1094 with
         | (tm1,t,guard) ->
             let uu____1102 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1102 with
              | (bs,comp) ->
                  let uu____1117 =
                    FStar_List.fold_left
                      (fun uu____1134  ->
                         fun uu____1135  ->
                           match (uu____1134, uu____1135) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1184 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1184 with
                                | (u,uu____1199,g_u) ->
                                    let uu____1207 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1207,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1117 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let ret_typ = comp_to_typ comp1 in
                       let uu____1240 =
                         FStar_TypeChecker_Rel.try_teq false goal.context
                           ret_typ goal.goal_ty in
                       (match uu____1240 with
                        | None  ->
                            let uu____1243 =
                              let uu____1244 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____1245 =
                                FStar_Syntax_Print.term_to_string ret_typ in
                              let uu____1246 =
                                FStar_Syntax_Print.term_to_string
                                  goal.goal_ty in
                              FStar_Util.format3
                                "apply: does not unify with goal: %s : %s vs %s"
                                uu____1244 uu____1245 uu____1246 in
                            fail uu____1243
                        | Some g ->
                            let g1 =
                              let uu____1249 =
                                FStar_TypeChecker_Rel.solve_deferred_constraints
                                  goal.context g in
                              FStar_All.pipe_right uu____1249
                                FStar_TypeChecker_Rel.resolve_implicits in
                            let solution =
                              FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1 None
                                (goal.context).FStar_TypeChecker_Env.range in
                            let implicits1 =
                              FStar_All.pipe_right
                                implicits.FStar_TypeChecker_Env.implicits
                                (FStar_List.filter
                                   (fun uu____1283  ->
                                      match uu____1283 with
                                      | (uu____1290,uu____1291,uu____1292,tm2,uu____1294,uu____1295)
                                          ->
                                          let uu____1296 =
                                            FStar_Syntax_Util.head_and_args
                                              tm2 in
                                          (match uu____1296 with
                                           | (hd1,uu____1307) ->
                                               let uu____1322 =
                                                 let uu____1323 =
                                                   FStar_Syntax_Subst.compress
                                                     hd1 in
                                                 uu____1323.FStar_Syntax_Syntax.n in
                                               (match uu____1322 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    uu____1326 -> true
                                                | uu____1335 -> false)))) in
                            (solve goal solution;
                             (let is_free_uvar uv t1 =
                                let free_uvars =
                                  let uu____1346 =
                                    let uu____1350 =
                                      FStar_Syntax_Free.uvars t1 in
                                    FStar_Util.set_elements uu____1350 in
                                  FStar_List.map FStar_Pervasives.fst
                                    uu____1346 in
                                FStar_List.existsML
                                  (fun u  ->
                                     FStar_Syntax_Unionfind.equiv u uv)
                                  free_uvars in
                              let appears uv goals =
                                FStar_List.existsML
                                  (fun g'  -> is_free_uvar uv g'.goal_ty)
                                  goals in
                              let checkone t1 goals =
                                let uu____1378 =
                                  FStar_Syntax_Util.head_and_args t1 in
                                match uu____1378 with
                                | (hd1,uu____1389) ->
                                    (match hd1.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (uv,uu____1405) -> appears uv goals
                                     | uu____1418 -> false) in
                              let sub_goals =
                                FStar_All.pipe_right implicits1
                                  (FStar_List.map
                                     (fun uu____1435  ->
                                        match uu____1435 with
                                        | (_msg,_env,_uvar,term,typ,uu____1447)
                                            ->
                                            let uu____1448 =
                                              bnorm goal.context term in
                                            let uu____1449 =
                                              bnorm goal.context typ in
                                            {
                                              context = (goal.context);
                                              witness = uu____1448;
                                              goal_ty = uu____1449
                                            })) in
                              let rec filter' f xs =
                                match xs with
                                | [] -> []
                                | x::xs1 ->
                                    let uu____1481 = f x xs1 in
                                    if uu____1481
                                    then
                                      let uu____1483 = filter' f xs1 in x ::
                                        uu____1483
                                    else filter' f xs1 in
                              let sub_goals1 =
                                filter'
                                  (fun g2  ->
                                     fun goals  ->
                                       let uu____1491 =
                                         checkone g2.witness goals in
                                       Prims.op_Negation uu____1491)
                                  sub_goals in
                              let uu____1492 =
                                add_implicits
                                  g1.FStar_TypeChecker_Env.implicits in
                              bind uu____1492
                                (fun uu____1494  ->
                                   bind dismiss
                                     (fun uu____1495  -> add_goals sub_goals1))))))))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1502 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1502 with
         | (tm1,t,guard) ->
             let uu____1510 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1510 with
              | (bs,comp) ->
                  let uu____1525 =
                    FStar_List.fold_left
                      (fun uu____1542  ->
                         fun uu____1543  ->
                           match (uu____1542, uu____1543) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1592 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1592 with
                                | (u,uu____1607,g_u) ->
                                    let uu____1615 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1615,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1525 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let uu____1647 =
                         let uu____1654 =
                           let uu____1660 =
                             FStar_Syntax_Util.comp_to_comp_typ comp1 in
                           uu____1660.FStar_Syntax_Syntax.effect_args in
                         match uu____1654 with
                         | pre::post::uu____1669 -> ((fst pre), (fst post))
                         | uu____1699 ->
                             failwith "apply_lemma: impossible: not a lemma" in
                       (match uu____1647 with
                        | (pre,post) ->
                            let uu____1722 =
                              let uu____1724 =
                                FStar_Syntax_Util.mk_squash post in
                              FStar_TypeChecker_Rel.try_teq false
                                goal.context uu____1724 goal.goal_ty in
                            (match uu____1722 with
                             | None  ->
                                 let uu____1726 =
                                   let uu____1727 =
                                     let uu____1728 =
                                       FStar_Syntax_Util.mk_squash post in
                                     FStar_Syntax_Print.term_to_string
                                       uu____1728 in
                                   let uu____1729 =
                                     FStar_Syntax_Print.term_to_string
                                       goal.goal_ty in
                                   FStar_Util.format2
                                     "apply_lemma: does not unify with goal: %s vs %s"
                                     uu____1727 uu____1729 in
                                 fail uu____1726
                             | Some g ->
                                 let g1 =
                                   let uu____1732 =
                                     FStar_TypeChecker_Rel.solve_deferred_constraints
                                       goal.context g in
                                   FStar_All.pipe_right uu____1732
                                     FStar_TypeChecker_Rel.resolve_implicits in
                                 let solution =
                                   FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                     None
                                     (goal.context).FStar_TypeChecker_Env.range in
                                 let implicits1 =
                                   FStar_All.pipe_right
                                     implicits.FStar_TypeChecker_Env.implicits
                                     (FStar_List.filter
                                        (fun uu____1766  ->
                                           match uu____1766 with
                                           | (uu____1773,uu____1774,uu____1775,tm2,uu____1777,uu____1778)
                                               ->
                                               let uu____1779 =
                                                 FStar_Syntax_Util.head_and_args
                                                   tm2 in
                                               (match uu____1779 with
                                                | (hd1,uu____1790) ->
                                                    let uu____1805 =
                                                      let uu____1806 =
                                                        FStar_Syntax_Subst.compress
                                                          hd1 in
                                                      uu____1806.FStar_Syntax_Syntax.n in
                                                    (match uu____1805 with
                                                     | FStar_Syntax_Syntax.Tm_uvar
                                                         uu____1809 -> true
                                                     | uu____1818 -> false)))) in
                                 (solve goal solution;
                                  (let is_free_uvar uv t1 =
                                     let free_uvars =
                                       let uu____1829 =
                                         let uu____1833 =
                                           FStar_Syntax_Free.uvars t1 in
                                         FStar_Util.set_elements uu____1833 in
                                       FStar_List.map FStar_Pervasives.fst
                                         uu____1829 in
                                     FStar_List.existsML
                                       (fun u  ->
                                          FStar_Syntax_Unionfind.equiv u uv)
                                       free_uvars in
                                   let appears uv goals =
                                     FStar_List.existsML
                                       (fun g'  -> is_free_uvar uv g'.goal_ty)
                                       goals in
                                   let checkone t1 goals =
                                     let uu____1861 =
                                       FStar_Syntax_Util.head_and_args t1 in
                                     match uu____1861 with
                                     | (hd1,uu____1872) ->
                                         (match hd1.FStar_Syntax_Syntax.n
                                          with
                                          | FStar_Syntax_Syntax.Tm_uvar
                                              (uv,uu____1888) ->
                                              appears uv goals
                                          | uu____1901 -> false) in
                                   let sub_goals =
                                     FStar_All.pipe_right implicits1
                                       (FStar_List.map
                                          (fun uu____1918  ->
                                             match uu____1918 with
                                             | (_msg,_env,_uvar,term,typ,uu____1930)
                                                 ->
                                                 let uu____1931 =
                                                   bnorm goal.context term in
                                                 let uu____1932 =
                                                   bnorm goal.context typ in
                                                 {
                                                   context = (goal.context);
                                                   witness = uu____1931;
                                                   goal_ty = uu____1932
                                                 })) in
                                   let rec filter' f xs =
                                     match xs with
                                     | [] -> []
                                     | x::xs1 ->
                                         let uu____1964 = f x xs1 in
                                         if uu____1964
                                         then
                                           let uu____1966 = filter' f xs1 in
                                           x :: uu____1966
                                         else filter' f xs1 in
                                   let sub_goals1 =
                                     filter'
                                       (fun g2  ->
                                          fun goals  ->
                                            let uu____1974 =
                                              checkone g2.witness goals in
                                            Prims.op_Negation uu____1974)
                                       sub_goals in
                                   let pregoal =
                                     mk_irrelevant goal.context pre in
                                   let sub_goals2 =
                                     let uu____1978 =
                                       istrivial goal.context pregoal.goal_ty in
                                     if uu____1978
                                     then sub_goals1
                                     else pregoal :: sub_goals1 in
                                   let uu____1981 =
                                     add_implicits
                                       g1.FStar_TypeChecker_Env.implicits in
                                   bind uu____1981
                                     (fun uu____1983  ->
                                        bind dismiss
                                          (fun uu____1984  ->
                                             add_goals sub_goals2)))))))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         try
           let uu____1994 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
           match uu____1994 with
           | (t1,typ,guard) ->
               let uu____2002 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                   goal.goal_ty in
               if uu____2002
               then (solve goal t1; dismiss)
               else
                 (let msg =
                    let uu____2007 = FStar_Syntax_Print.term_to_string t1 in
                    let uu____2008 =
                      let uu____2009 = bnorm goal.context typ in
                      FStar_Syntax_Print.term_to_string uu____2009 in
                    let uu____2010 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____2007
                      uu____2008 uu____2010 in
                  fail msg)
         with
         | e ->
             let uu____2014 =
               let uu____2015 = FStar_Syntax_Print.term_to_string t in
               let uu____2016 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.format2 "Term is not typeable: %s (%s)" uu____2015
                 uu____2016 in
             fail uu____2014)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2023 =
           FStar_All.pipe_left mlog
             (fun uu____2028  ->
                let uu____2029 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2030 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2029
                  uu____2030) in
         bind uu____2023
           (fun uu____2031  ->
              let uu____2032 =
                let uu____2034 =
                  let uu____2035 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2035 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2034 in
              match uu____2032 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2042::(x,uu____2044)::(e,uu____2046)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2080 =
                    let uu____2081 = FStar_Syntax_Subst.compress x in
                    uu____2081.FStar_Syntax_Syntax.n in
                  (match uu____2080 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___94_2087 = goal in
                         let uu____2088 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2091 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___94_2087.context);
                           witness = uu____2088;
                           goal_ty = uu____2091
                         } in
                       replace_cur goal1
                   | uu____2094 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2095 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2099 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2099 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2114 = FStar_Util.set_mem x fns_ty in
           if uu____2114
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2117 =
                FStar_TypeChecker_Util.new_implicit_var "clear"
                  (goal.goal_ty).FStar_Syntax_Syntax.pos env' goal.goal_ty in
              match uu____2117 with
              | (u,uu____2126,g) ->
                  let uu____2134 =
                    let uu____2135 =
                      FStar_TypeChecker_Rel.teq_nosmt goal.context
                        goal.witness u in
                    Prims.op_Negation uu____2135 in
                  if uu____2134
                  then fail "clear: unification failed"
                  else
                    (let new_goal =
                       let uu___95_2139 = goal in
                       let uu____2140 = bnorm env' u in
                       {
                         context = env';
                         witness = uu____2140;
                         goal_ty = (uu___95_2139.goal_ty)
                       } in
                     bind dismiss (fun uu____2141  -> add_goals [new_goal]))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2148 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2148 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2163 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2163 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2177 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2177 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___96_2200 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2207 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2207 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2219 =
                 let uu____2220 = FStar_Syntax_Print.bv_to_string x in
                 let uu____2221 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____2220 uu____2221 in
               fail uu____2219
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2234 = revert_all_hd xs1 in
        bind uu____2234 (fun uu____2236  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___97_2246 = g in
           {
             context = ctx';
             witness = (uu___97_2246.witness);
             goal_ty = (uu___97_2246.goal_ty)
           } in
         bind dismiss (fun uu____2247  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___98_2257 = g in
           {
             context = ctx';
             witness = (uu___98_2257.witness);
             goal_ty = (uu___98_2257.goal_ty)
           } in
         bind dismiss (fun uu____2258  -> add_goals [g']))
let rec bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2279 = FStar_Syntax_Subst.compress t in
          uu____2279.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2302 =
                let uu____2312 = ff hd1 in
                let uu____2313 =
                  FStar_List.map
                    (fun uu____2321  ->
                       match uu____2321 with
                       | (a,q) -> let uu____2328 = ff a in (uu____2328, q))
                    args in
                (uu____2312, uu____2313) in
              FStar_Syntax_Syntax.Tm_app uu____2302
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2357 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2357 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2363 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2363 t' in
                   let uu____2364 =
                     let uu____2379 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2379, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2364)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2398 -> tn in
        f env
          (let uu___99_2399 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___99_2399.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos = (uu___99_2399.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___99_2399.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2433 = f x in
      bind uu____2433
        (fun y  ->
           let uu____2437 = mapM f xs in
           bind uu____2437 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2469 = FStar_Syntax_Subst.compress t in
          uu____2469.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2495 = ff hd1 in
              bind uu____2495
                (fun hd2  ->
                   let fa uu____2506 =
                     match uu____2506 with
                     | (a,q) ->
                         let uu____2514 = ff a in
                         bind uu____2514 (fun a1  -> ret (a1, q)) in
                   let uu____2521 = mapM fa args in
                   bind uu____2521
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2565 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2565 with
               | (bs1,t') ->
                   let uu____2571 =
                     let uu____2573 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2573 t' in
                   bind uu____2571
                     (fun t''  ->
                        let uu____2575 =
                          let uu____2576 =
                            let uu____2591 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2591, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2576 in
                        ret uu____2575))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2610 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___100_2612 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___100_2612.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___100_2612.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___100_2612.FStar_Syntax_Syntax.vars)
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
          let uu____2633 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2633 with
          | (t1,lcomp,g) ->
              let uu____2641 =
                (let uu____2642 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2642) ||
                  (let uu____2643 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2643) in
              if uu____2641
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2649 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env typ in
                 match uu____2649 with
                 | (ut,uvs,guard) ->
                     (log ps
                        (fun uu____2667  ->
                           let uu____2668 =
                             FStar_Syntax_Print.term_to_string t1 in
                           let uu____2669 =
                             FStar_Syntax_Print.term_to_string ut in
                           FStar_Util.print2
                             "Pointwise_rec: making equality %s = %s\n"
                             uu____2668 uu____2669);
                      (let g' =
                         let uu____2671 =
                           let uu____2672 =
                             FStar_TypeChecker_TcTerm.universe_of env typ in
                           FStar_Syntax_Util.mk_eq2 uu____2672 typ t1 ut in
                         mk_irrelevant env uu____2671 in
                       let uu____2673 = add_goals [g'] in
                       bind uu____2673
                         (fun uu____2675  ->
                            let uu____2676 =
                              bind tau
                                (fun uu____2678  ->
                                   let guard1 =
                                     let uu____2680 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env guard in
                                     FStar_All.pipe_right uu____2680
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env guard1;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.WHNF]
                                        env ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2676))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2691 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2691 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2712  ->
                   let uu____2713 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2713);
              bind dismiss_all
                (fun uu____2714  ->
                   let uu____2715 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2715
                     (fun gt'  ->
                        log ps
                          (fun uu____2719  ->
                             let uu____2720 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2720);
                        (let uu____2721 = push_goals gs in
                         bind uu____2721
                           (fun uu____2723  ->
                              add_goals
                                [(let uu___101_2724 = g in
                                  {
                                    context = (uu___101_2724.context);
                                    witness = (uu___101_2724.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2727 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2727 with
       | Some t ->
           let uu____2737 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2737 with
            | (hd1,args) ->
                let uu____2758 =
                  let uu____2766 =
                    let uu____2767 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2767.FStar_Syntax_Syntax.n in
                  (uu____2766, args) in
                (match uu____2758 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2777::(l,uu____2779)::(r,uu____2781)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.eq2_lid
                     ->
                     let uu____2815 =
                       let uu____2816 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____2816 in
                     if uu____2815
                     then
                       let uu____2818 =
                         let uu____2819 = FStar_Syntax_Print.term_to_string l in
                         let uu____2820 = FStar_Syntax_Print.term_to_string r in
                         FStar_Util.format2
                           "trefl: not a trivial equality (%s vs %s)"
                           uu____2819 uu____2820 in
                       fail uu____2818
                     else
                       (let t_unit1 = FStar_TypeChecker_Common.t_unit in
                        solve g t_unit1; dismiss)
                 | (hd2,uu____2827) ->
                     let uu____2838 =
                       let uu____2839 = FStar_Syntax_Print.term_to_string t in
                       FStar_Util.format1 "trefl: not an equality (%s)"
                         uu____2839 in
                     fail uu____2838))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___102_2849 = ps in
              {
                main_context = (uu___102_2849.main_context);
                main_goal = (uu___102_2849.main_goal);
                all_implicits = (uu___102_2849.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___102_2849.smt_goals)
              })
       | uu____2850 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___103_2858 = ps in
              {
                main_context = (uu___103_2858.main_context);
                main_goal = (uu___103_2858.main_goal);
                all_implicits = (uu___103_2858.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___103_2858.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2862 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2876 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2876 with
         | (t1,typ,guard) ->
             let uu____2886 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2886 with
              | (hd1,args) ->
                  let uu____2915 =
                    let uu____2923 =
                      let uu____2924 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2924.FStar_Syntax_Syntax.n in
                    (uu____2923, args) in
                  (match uu____2915 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2937)::(q,uu____2939)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___104_2968 = g in
                         let uu____2969 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2969;
                           witness = (uu___104_2968.witness);
                           goal_ty = (uu___104_2968.goal_ty)
                         } in
                       let g2 =
                         let uu___105_2971 = g in
                         let uu____2972 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2972;
                           witness = (uu___105_2971.witness);
                           goal_ty = (uu___105_2971.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____2975  ->
                            let uu____2976 = add_goals [g1; g2] in
                            bind uu____2976
                              (fun uu____2980  ->
                                 let uu____2981 =
                                   let uu____2984 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____2985 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____2984, uu____2985) in
                                 ret uu____2981))
                   | uu____2988 ->
                       let uu____2996 =
                         let uu____2997 =
                           FStar_Syntax_Print.term_to_string typ in
                         FStar_Util.format1 "Not a disjunction: %s"
                           uu____2997 in
                       fail uu____2996)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____3003 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____3007 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____3011 -> false
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
      let uu____3031 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____3031 with
      | (u,uu____3039,g_u) ->
          let g = { context = env; witness = u; goal_ty = typ } in
          {
            main_context = env;
            main_goal = g;
            all_implicits = [];
            goals = [g];
            smt_goals = []
          }