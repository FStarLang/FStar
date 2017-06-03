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
           TacFailure uu____519 in
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
       let uu____1082 = istrivial goal.context goal.goal_ty in
       if uu____1082
       then
         let t_unit1 = FStar_TypeChecker_Common.t_unit in
         (solve goal t_unit1; dismiss)
       else
         (let uu____1089 =
            let uu____1090 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            FStar_Util.format1 "Not a trivial goal: %s" uu____1090 in
          fail uu____1089))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1097 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1097 with
         | (tm1,t,guard) ->
             let uu____1105 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1105 with
              | (bs,comp) ->
                  let uu____1120 =
                    FStar_List.fold_left
                      (fun uu____1137  ->
                         fun uu____1138  ->
                           match (uu____1137, uu____1138) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1187 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1187 with
                                | (u,uu____1202,g_u) ->
                                    let uu____1210 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1210,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1120 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let ret_typ = comp_to_typ comp1 in
                       let uu____1243 =
                         FStar_TypeChecker_Rel.try_teq false goal.context
                           ret_typ goal.goal_ty in
                       (match uu____1243 with
                        | None  ->
                            let uu____1246 =
                              let uu____1247 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____1248 =
                                FStar_Syntax_Print.term_to_string ret_typ in
                              let uu____1249 =
                                FStar_Syntax_Print.term_to_string
                                  goal.goal_ty in
                              FStar_Util.format3
                                "apply: does not unify with goal: %s : %s vs %s"
                                uu____1247 uu____1248 uu____1249 in
                            fail uu____1246
                        | Some g ->
                            let g1 =
                              let uu____1252 =
                                FStar_TypeChecker_Rel.solve_deferred_constraints
                                  goal.context g in
                              FStar_All.pipe_right uu____1252
                                FStar_TypeChecker_Rel.resolve_implicits in
                            let solution =
                              FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1 None
                                (goal.context).FStar_TypeChecker_Env.range in
                            let implicits1 =
                              FStar_All.pipe_right
                                implicits.FStar_TypeChecker_Env.implicits
                                (FStar_List.filter
                                   (fun uu____1286  ->
                                      match uu____1286 with
                                      | (uu____1293,uu____1294,uu____1295,tm2,uu____1297,uu____1298)
                                          ->
                                          let uu____1299 =
                                            FStar_Syntax_Util.head_and_args
                                              tm2 in
                                          (match uu____1299 with
                                           | (hd1,uu____1310) ->
                                               let uu____1325 =
                                                 let uu____1326 =
                                                   FStar_Syntax_Subst.compress
                                                     hd1 in
                                                 uu____1326.FStar_Syntax_Syntax.n in
                                               (match uu____1325 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    uu____1329 -> true
                                                | uu____1338 -> false)))) in
                            (solve goal solution;
                             (let is_free_uvar uv t1 =
                                let free_uvars =
                                  let uu____1349 =
                                    let uu____1353 =
                                      FStar_Syntax_Free.uvars t1 in
                                    FStar_Util.set_elements uu____1353 in
                                  FStar_List.map FStar_Pervasives.fst
                                    uu____1349 in
                                FStar_List.existsML
                                  (fun u  ->
                                     FStar_Syntax_Unionfind.equiv u uv)
                                  free_uvars in
                              let appears uv goals =
                                FStar_List.existsML
                                  (fun g'  -> is_free_uvar uv g'.goal_ty)
                                  goals in
                              let checkone t1 goals =
                                let uu____1381 =
                                  FStar_Syntax_Util.head_and_args t1 in
                                match uu____1381 with
                                | (hd1,uu____1392) ->
                                    (match hd1.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (uv,uu____1408) -> appears uv goals
                                     | uu____1421 -> false) in
                              let sub_goals =
                                FStar_All.pipe_right implicits1
                                  (FStar_List.map
                                     (fun uu____1438  ->
                                        match uu____1438 with
                                        | (_msg,_env,_uvar,term,typ,uu____1450)
                                            ->
                                            let uu____1451 =
                                              bnorm goal.context term in
                                            let uu____1452 =
                                              bnorm goal.context typ in
                                            {
                                              context = (goal.context);
                                              witness = uu____1451;
                                              goal_ty = uu____1452
                                            })) in
                              let rec filter' f xs =
                                match xs with
                                | [] -> []
                                | x::xs1 ->
                                    let uu____1484 = f x xs1 in
                                    if uu____1484
                                    then
                                      let uu____1486 = filter' f xs1 in x ::
                                        uu____1486
                                    else filter' f xs1 in
                              let sub_goals1 =
                                filter'
                                  (fun g2  ->
                                     fun goals  ->
                                       let uu____1494 =
                                         checkone g2.witness goals in
                                       Prims.op_Negation uu____1494)
                                  sub_goals in
                              let uu____1495 =
                                add_implicits
                                  g1.FStar_TypeChecker_Env.implicits in
                              bind uu____1495
                                (fun uu____1497  ->
                                   bind dismiss
                                     (fun uu____1498  -> add_goals sub_goals1))))))))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1505 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1505 with
         | (tm1,t,guard) ->
             let uu____1513 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1513 with
              | (bs,comp) ->
                  let uu____1528 =
                    FStar_List.fold_left
                      (fun uu____1545  ->
                         fun uu____1546  ->
                           match (uu____1545, uu____1546) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1595 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1595 with
                                | (u,uu____1610,g_u) ->
                                    let uu____1618 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1618,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1528 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let uu____1650 =
                         let uu____1657 =
                           let uu____1663 =
                             FStar_Syntax_Util.comp_to_comp_typ comp1 in
                           uu____1663.FStar_Syntax_Syntax.effect_args in
                         match uu____1657 with
                         | pre::post::uu____1672 -> ((fst pre), (fst post))
                         | uu____1702 ->
                             failwith "apply_lemma: impossible: not a lemma" in
                       (match uu____1650 with
                        | (pre,post) ->
                            let uu____1725 =
                              let uu____1727 =
                                FStar_Syntax_Util.mk_squash post in
                              FStar_TypeChecker_Rel.try_teq false
                                goal.context uu____1727 goal.goal_ty in
                            (match uu____1725 with
                             | None  ->
                                 let uu____1729 =
                                   let uu____1730 =
                                     let uu____1731 =
                                       FStar_Syntax_Util.mk_squash post in
                                     FStar_Syntax_Print.term_to_string
                                       uu____1731 in
                                   let uu____1732 =
                                     FStar_Syntax_Print.term_to_string
                                       goal.goal_ty in
                                   FStar_Util.format2
                                     "apply_lemma: does not unify with goal: %s vs %s"
                                     uu____1730 uu____1732 in
                                 fail uu____1729
                             | Some g ->
                                 let g1 =
                                   let uu____1735 =
                                     FStar_TypeChecker_Rel.solve_deferred_constraints
                                       goal.context g in
                                   FStar_All.pipe_right uu____1735
                                     FStar_TypeChecker_Rel.resolve_implicits in
                                 let solution =
                                   FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                     None
                                     (goal.context).FStar_TypeChecker_Env.range in
                                 let implicits1 =
                                   FStar_All.pipe_right
                                     implicits.FStar_TypeChecker_Env.implicits
                                     (FStar_List.filter
                                        (fun uu____1769  ->
                                           match uu____1769 with
                                           | (uu____1776,uu____1777,uu____1778,tm2,uu____1780,uu____1781)
                                               ->
                                               let uu____1782 =
                                                 FStar_Syntax_Util.head_and_args
                                                   tm2 in
                                               (match uu____1782 with
                                                | (hd1,uu____1793) ->
                                                    let uu____1808 =
                                                      let uu____1809 =
                                                        FStar_Syntax_Subst.compress
                                                          hd1 in
                                                      uu____1809.FStar_Syntax_Syntax.n in
                                                    (match uu____1808 with
                                                     | FStar_Syntax_Syntax.Tm_uvar
                                                         uu____1812 -> true
                                                     | uu____1821 -> false)))) in
                                 (solve goal solution;
                                  (let is_free_uvar uv t1 =
                                     let free_uvars =
                                       let uu____1832 =
                                         let uu____1836 =
                                           FStar_Syntax_Free.uvars t1 in
                                         FStar_Util.set_elements uu____1836 in
                                       FStar_List.map FStar_Pervasives.fst
                                         uu____1832 in
                                     FStar_List.existsML
                                       (fun u  ->
                                          FStar_Syntax_Unionfind.equiv u uv)
                                       free_uvars in
                                   let appears uv goals =
                                     FStar_List.existsML
                                       (fun g'  -> is_free_uvar uv g'.goal_ty)
                                       goals in
                                   let checkone t1 goals =
                                     let uu____1864 =
                                       FStar_Syntax_Util.head_and_args t1 in
                                     match uu____1864 with
                                     | (hd1,uu____1875) ->
                                         (match hd1.FStar_Syntax_Syntax.n
                                          with
                                          | FStar_Syntax_Syntax.Tm_uvar
                                              (uv,uu____1891) ->
                                              appears uv goals
                                          | uu____1904 -> false) in
                                   let sub_goals =
                                     FStar_All.pipe_right implicits1
                                       (FStar_List.map
                                          (fun uu____1921  ->
                                             match uu____1921 with
                                             | (_msg,_env,_uvar,term,typ,uu____1933)
                                                 ->
                                                 let uu____1934 =
                                                   bnorm goal.context term in
                                                 let uu____1935 =
                                                   bnorm goal.context typ in
                                                 {
                                                   context = (goal.context);
                                                   witness = uu____1934;
                                                   goal_ty = uu____1935
                                                 })) in
                                   let rec filter' f xs =
                                     match xs with
                                     | [] -> []
                                     | x::xs1 ->
                                         let uu____1967 = f x xs1 in
                                         if uu____1967
                                         then
                                           let uu____1969 = filter' f xs1 in
                                           x :: uu____1969
                                         else filter' f xs1 in
                                   let sub_goals1 =
                                     filter'
                                       (fun g2  ->
                                          fun goals  ->
                                            let uu____1977 =
                                              checkone g2.witness goals in
                                            Prims.op_Negation uu____1977)
                                       sub_goals in
                                   let pregoal =
                                     mk_irrelevant goal.context pre in
                                   let sub_goals2 =
                                     let uu____1981 =
                                       istrivial goal.context pregoal.goal_ty in
                                     if uu____1981
                                     then sub_goals1
                                     else pregoal :: sub_goals1 in
                                   let uu____1984 =
                                     add_implicits
                                       g1.FStar_TypeChecker_Env.implicits in
                                   bind uu____1984
                                     (fun uu____1986  ->
                                        bind dismiss
                                          (fun uu____1987  ->
                                             add_goals sub_goals2)))))))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         try
           let uu____1997 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
           match uu____1997 with
           | (t1,typ,guard) ->
               let uu____2005 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                   goal.goal_ty in
               if uu____2005
               then (solve goal t1; dismiss)
               else
                 (let msg =
                    let uu____2010 = FStar_Syntax_Print.term_to_string t1 in
                    let uu____2011 =
                      let uu____2012 = bnorm goal.context typ in
                      FStar_Syntax_Print.term_to_string uu____2012 in
                    let uu____2013 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____2010
                      uu____2011 uu____2013 in
                  fail msg)
         with
         | e ->
             let uu____2017 =
               let uu____2018 = FStar_Syntax_Print.term_to_string t in
               let uu____2019 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.format2 "Term is not typeable: %s (%s)" uu____2018
                 uu____2019 in
             fail uu____2017)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2026 =
           FStar_All.pipe_left mlog
             (fun uu____2031  ->
                let uu____2032 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2033 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2032
                  uu____2033) in
         bind uu____2026
           (fun uu____2034  ->
              let uu____2035 =
                let uu____2037 =
                  let uu____2038 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2038 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2037 in
              match uu____2035 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2045::(x,uu____2047)::(e,uu____2049)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2083 =
                    let uu____2084 = FStar_Syntax_Subst.compress x in
                    uu____2084.FStar_Syntax_Syntax.n in
                  (match uu____2083 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___94_2090 = goal in
                         let uu____2091 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2094 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___94_2090.context);
                           witness = uu____2091;
                           goal_ty = uu____2094
                         } in
                       replace_cur goal1
                   | uu____2097 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2098 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2102 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2102 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2117 = FStar_Util.set_mem x fns_ty in
           if uu____2117
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2120 =
                FStar_TypeChecker_Util.new_implicit_var "clear"
                  (goal.goal_ty).FStar_Syntax_Syntax.pos env' goal.goal_ty in
              match uu____2120 with
              | (u,uu____2129,g) ->
                  let uu____2137 =
                    let uu____2138 =
                      FStar_TypeChecker_Rel.teq_nosmt goal.context
                        goal.witness u in
                    Prims.op_Negation uu____2138 in
                  if uu____2137
                  then fail "clear: unification failed"
                  else
                    (let new_goal =
                       let uu___95_2142 = goal in
                       let uu____2143 = bnorm env' u in
                       {
                         context = env';
                         witness = uu____2143;
                         goal_ty = (uu___95_2142.goal_ty)
                       } in
                     bind dismiss (fun uu____2144  -> add_goals [new_goal]))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2151 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2151 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2166 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2166 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2180 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2180 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___96_2203 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2210 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2210 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2222 =
                 let uu____2223 = FStar_Syntax_Print.bv_to_string x in
                 let uu____2224 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____2223 uu____2224 in
               fail uu____2222
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2237 = revert_all_hd xs1 in
        bind uu____2237 (fun uu____2239  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___97_2249 = g in
           {
             context = ctx';
             witness = (uu___97_2249.witness);
             goal_ty = (uu___97_2249.goal_ty)
           } in
         bind dismiss (fun uu____2250  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___98_2260 = g in
           {
             context = ctx';
             witness = (uu___98_2260.witness);
             goal_ty = (uu___98_2260.goal_ty)
           } in
         bind dismiss (fun uu____2261  -> add_goals [g']))
let rec bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2282 = FStar_Syntax_Subst.compress t in
          uu____2282.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2305 =
                let uu____2315 = ff hd1 in
                let uu____2316 =
                  FStar_List.map
                    (fun uu____2324  ->
                       match uu____2324 with
                       | (a,q) -> let uu____2331 = ff a in (uu____2331, q))
                    args in
                (uu____2315, uu____2316) in
              FStar_Syntax_Syntax.Tm_app uu____2305
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2360 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2360 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2366 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2366 t' in
                   let uu____2367 =
                     let uu____2382 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2382, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2367)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2401 -> tn in
        f env
          (let uu___99_2402 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___99_2402.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos = (uu___99_2402.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___99_2402.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2436 = f x in
      bind uu____2436
        (fun y  ->
           let uu____2440 = mapM f xs in
           bind uu____2440 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2472 = FStar_Syntax_Subst.compress t in
          uu____2472.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2498 = ff hd1 in
              bind uu____2498
                (fun hd2  ->
                   let fa uu____2509 =
                     match uu____2509 with
                     | (a,q) ->
                         let uu____2517 = ff a in
                         bind uu____2517 (fun a1  -> ret (a1, q)) in
                   let uu____2524 = mapM fa args in
                   bind uu____2524
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2568 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2568 with
               | (bs1,t') ->
                   let uu____2574 =
                     let uu____2576 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2576 t' in
                   bind uu____2574
                     (fun t''  ->
                        let uu____2578 =
                          let uu____2579 =
                            let uu____2594 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2594, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2579 in
                        ret uu____2578))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2613 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___100_2615 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___100_2615.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___100_2615.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___100_2615.FStar_Syntax_Syntax.vars)
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
          let uu____2636 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2636 with
          | (t1,lcomp,g) ->
              let uu____2644 =
                (let uu____2645 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2645) ||
                  (let uu____2646 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2646) in
              if uu____2644
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2652 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env typ in
                 match uu____2652 with
                 | (ut,uvs,guard) ->
                     (log ps
                        (fun uu____2670  ->
                           let uu____2671 =
                             FStar_Syntax_Print.term_to_string t1 in
                           let uu____2672 =
                             FStar_Syntax_Print.term_to_string ut in
                           FStar_Util.print2
                             "Pointwise_rec: making equality %s = %s\n"
                             uu____2671 uu____2672);
                      (let g' =
                         let uu____2674 =
                           let uu____2675 =
                             FStar_TypeChecker_TcTerm.universe_of env typ in
                           FStar_Syntax_Util.mk_eq2 uu____2675 typ t1 ut in
                         mk_irrelevant env uu____2674 in
                       let uu____2676 = add_goals [g'] in
                       bind uu____2676
                         (fun uu____2678  ->
                            let uu____2679 =
                              bind tau
                                (fun uu____2681  ->
                                   let guard1 =
                                     let uu____2683 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env guard in
                                     FStar_All.pipe_right uu____2683
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env guard1;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.WHNF]
                                        env ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2679))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2694 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2694 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2715  ->
                   let uu____2716 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2716);
              bind dismiss_all
                (fun uu____2717  ->
                   let uu____2718 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2718
                     (fun gt'  ->
                        log ps
                          (fun uu____2722  ->
                             let uu____2723 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2723);
                        (let uu____2724 = push_goals gs in
                         bind uu____2724
                           (fun uu____2726  ->
                              add_goals
                                [(let uu___101_2727 = g in
                                  {
                                    context = (uu___101_2727.context);
                                    witness = (uu___101_2727.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2730 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2730 with
       | Some t ->
           let uu____2740 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2740 with
            | (hd1,args) ->
                let uu____2761 =
                  let uu____2769 =
                    let uu____2770 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2770.FStar_Syntax_Syntax.n in
                  (uu____2769, args) in
                (match uu____2761 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2780::(l,uu____2782)::(r,uu____2784)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.eq2_lid
                     ->
                     let uu____2818 =
                       let uu____2819 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____2819 in
                     if uu____2818
                     then
                       let uu____2821 =
                         let uu____2822 = FStar_Syntax_Print.term_to_string l in
                         let uu____2823 = FStar_Syntax_Print.term_to_string r in
                         FStar_Util.format2
                           "trefl: not a trivial equality (%s vs %s)"
                           uu____2822 uu____2823 in
                       fail uu____2821
                     else
                       (let t_unit1 = FStar_TypeChecker_Common.t_unit in
                        solve g t_unit1; dismiss)
                 | (hd2,uu____2830) ->
                     let uu____2841 =
                       let uu____2842 = FStar_Syntax_Print.term_to_string t in
                       FStar_Util.format1 "trefl: not an equality (%s)"
                         uu____2842 in
                     fail uu____2841))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___102_2852 = ps in
              {
                main_context = (uu___102_2852.main_context);
                main_goal = (uu___102_2852.main_goal);
                all_implicits = (uu___102_2852.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___102_2852.smt_goals)
              })
       | uu____2853 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___103_2861 = ps in
              {
                main_context = (uu___103_2861.main_context);
                main_goal = (uu___103_2861.main_goal);
                all_implicits = (uu___103_2861.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___103_2861.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2865 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2879 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2879 with
         | (t1,typ,guard) ->
             let uu____2889 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2889 with
              | (hd1,args) ->
                  let uu____2918 =
                    let uu____2926 =
                      let uu____2927 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2927.FStar_Syntax_Syntax.n in
                    (uu____2926, args) in
                  (match uu____2918 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2940)::(q,uu____2942)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___104_2971 = g in
                         let uu____2972 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2972;
                           witness = (uu___104_2971.witness);
                           goal_ty = (uu___104_2971.goal_ty)
                         } in
                       let g2 =
                         let uu___105_2974 = g in
                         let uu____2975 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2975;
                           witness = (uu___105_2974.witness);
                           goal_ty = (uu___105_2974.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____2978  ->
                            let uu____2979 = add_goals [g1; g2] in
                            bind uu____2979
                              (fun uu____2983  ->
                                 let uu____2984 =
                                   let uu____2987 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____2988 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____2987, uu____2988) in
                                 ret uu____2984))
                   | uu____2991 ->
                       let uu____2999 =
                         let uu____3000 =
                           FStar_Syntax_Print.term_to_string typ in
                         FStar_Util.format1 "Not a disjunction: %s"
                           uu____3000 in
                       fail uu____2999)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____3006 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____3010 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____3014 -> false
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
      let uu____3034 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____3034 with
      | (u,uu____3042,g_u) ->
          let g = { context = env; witness = u; goal_ty = typ } in
          {
            main_context = env;
            main_goal = g;
            all_implicits = [];
            goals = [g];
            smt_goals = []
          }