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
let mk_irrelevant: env -> FStar_Syntax_Syntax.typ -> goal =
  fun env  ->
    fun phi  ->
      let typ = FStar_Syntax_Util.mk_squash phi in
      let uu____360 =
        FStar_TypeChecker_Util.new_implicit_var "mk_irrelevant"
          phi.FStar_Syntax_Syntax.pos env typ in
      match uu____360 with
      | (u,uu____368,g_u) -> { context = env; witness = u; goal_ty = typ }
let dump_goal ps goal =
  let uu____389 = goal_to_string goal in tacprint uu____389
let dump_cur: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____397 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____400 = FStar_List.hd ps.goals in dump_goal ps uu____400))
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____410 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____410);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____416 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____416);
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
      let uu____453 = FStar_ST.read tac_verb_dbg in
      match uu____453 with
      | None  ->
          ((let uu____459 =
              let uu____461 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              Some uu____461 in
            FStar_ST.write tac_verb_dbg uu____459);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____487 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____487 then dump_proofstate ps "TACTING FAILING" else ());
       Failed (msg, ps))
let fail1 msg x = let uu____502 = FStar_Util.format1 msg x in fail uu____502
let fail2 msg x y =
  let uu____521 = FStar_Util.format2 msg x y in fail uu____521
let fail3 msg x y z =
  let uu____545 = FStar_Util.format3 msg x y z in fail uu____545
let trytac t =
  mk_tac
    (fun ps  ->
       let tx = FStar_Syntax_Unionfind.new_transaction () in
       let uu____560 = run t ps in
       match uu____560 with
       | Success (a,q) ->
           (FStar_Syntax_Unionfind.commit tx; Success ((Some a), q))
       | Failed (uu____569,uu____570) ->
           (FStar_Syntax_Unionfind.rollback tx; Success (None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____579  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____586 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____586
      then ()
      else
        (let uu____588 =
           let uu____589 =
             let uu____590 = FStar_Syntax_Print.term_to_string solution in
             let uu____591 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____592 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____590
               uu____591 uu____592 in
           TacFailure uu____589 in
         raise uu____588)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____595 =
         let uu___78_596 = p in
         let uu____597 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_596.main_context);
           main_goal = (uu___78_596.main_goal);
           all_implicits = (uu___78_596.all_implicits);
           goals = uu____597;
           smt_goals = (uu___78_596.smt_goals)
         } in
       set uu____595)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_601 = p in
          {
            main_context = (uu___79_601.main_context);
            main_goal = (uu___79_601.main_goal);
            all_implicits = (uu___79_601.all_implicits);
            goals = [];
            smt_goals = (uu___79_601.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_610 = p in
            {
              main_context = (uu___80_610.main_context);
              main_goal = (uu___80_610.main_goal);
              all_implicits = (uu___80_610.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_610.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_619 = p in
            {
              main_context = (uu___81_619.main_context);
              main_goal = (uu___81_619.main_goal);
              all_implicits = (uu___81_619.all_implicits);
              goals = (uu___81_619.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_628 = p in
            {
              main_context = (uu___82_628.main_context);
              main_goal = (uu___82_628.main_goal);
              all_implicits = (uu___82_628.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___82_628.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_637 = p in
            {
              main_context = (uu___83_637.main_context);
              main_goal = (uu___83_637.main_goal);
              all_implicits = (uu___83_637.all_implicits);
              goals = (uu___83_637.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____643  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_650 = p in
            {
              main_context = (uu___84_650.main_context);
              main_goal = (uu___84_650.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_650.goals);
              smt_goals = (uu___84_650.smt_goals)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____660 = FStar_Syntax_Util.un_squash t in
    match uu____660 with
    | Some t' ->
        let uu____669 =
          let uu____670 = FStar_Syntax_Subst.compress t' in
          uu____670.FStar_Syntax_Syntax.n in
        (match uu____669 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____674 -> false)
    | uu____675 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____682 = FStar_Syntax_Util.un_squash t in
    match uu____682 with
    | Some t' ->
        let uu____691 =
          let uu____692 = FStar_Syntax_Subst.compress t' in
          uu____692.FStar_Syntax_Syntax.n in
        (match uu____691 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____696 -> false)
    | uu____697 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____709 = is_irrelevant g in
       if uu____709
       then bind dismiss (fun uu____711  -> add_smt_goals [g])
       else
         (let uu____713 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____713))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____743 =
         try let uu____760 = FStar_List.splitAt n1 p.goals in ret uu____760
         with | uu____775 -> fail "divide: not enough goals" in
       bind uu____743
         (fun uu____786  ->
            match uu____786 with
            | (lgs,rgs) ->
                let lp =
                  let uu___85_801 = p in
                  {
                    main_context = (uu___85_801.main_context);
                    main_goal = (uu___85_801.main_goal);
                    all_implicits = (uu___85_801.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___86_803 = p in
                  {
                    main_context = (uu___86_803.main_context);
                    main_goal = (uu___86_803.main_goal);
                    all_implicits = (uu___86_803.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____804 = set lp in
                bind uu____804
                  (fun uu____808  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____815 = set rp in
                               bind uu____815
                                 (fun uu____819  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___87_827 = p in
                                                {
                                                  main_context =
                                                    (uu___87_827.main_context);
                                                  main_goal =
                                                    (uu___87_827.main_goal);
                                                  all_implicits =
                                                    (uu___87_827.all_implicits);
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
                                              let uu____828 = set p' in
                                              bind uu____828
                                                (fun uu____832  -> ret (a, b))))))))))
let focus_cur_goal f =
  let uu____845 = divide (Prims.parse_int "1") f idtac in
  bind uu____845 (fun uu____851  -> match uu____851 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____872::uu____873 ->
           let uu____875 =
             let uu____880 = map tau in
             divide (Prims.parse_int "1") tau uu____880 in
           bind uu____875
             (fun uu____888  -> match uu____888 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____911 =
        bind t1
          (fun uu____913  ->
             let uu____914 = map t2 in
             bind uu____914 (fun uu____918  -> ret ())) in
      focus_cur_goal uu____911
let arrow_one:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.comp) option
  =
  fun t  ->
    let uu____929 =
      let uu____930 = FStar_Syntax_Subst.compress t in
      uu____930.FStar_Syntax_Syntax.n in
    match uu____929 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) -> Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____991 =
          let uu____996 =
            let uu____997 = FStar_Syntax_Util.arrow bs c in
            FStar_Syntax_Syntax.mk_Total uu____997 in
          (b, uu____996) in
        Some uu____991
    | uu____1004 -> None
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____1013 = arrow_one goal.goal_ty in
       match uu____1013 with
       | Some (b,c) ->
           let uu____1024 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1024 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1044 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1047 =
                  let uu____1048 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1048 in
                if uu____1047
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1061 =
                     FStar_TypeChecker_Util.new_implicit_var "intro"
                       typ'.FStar_Syntax_Syntax.pos env' typ' in
                   match uu____1061 with
                   | (u,uu____1072,g) ->
                       let uu____1080 =
                         let uu____1081 = FStar_Syntax_Util.abs [b1] u None in
                         FStar_TypeChecker_Rel.teq_nosmt goal.context
                           goal.witness uu____1081 in
                       if uu____1080
                       then
                         let uu____1094 =
                           let uu____1096 =
                             let uu___90_1097 = goal in
                             let uu____1098 = bnorm env' u in
                             let uu____1099 = bnorm env' typ' in
                             {
                               context = env';
                               witness = uu____1098;
                               goal_ty = uu____1099
                             } in
                           replace_cur uu____1096 in
                         bind uu____1094 (fun uu____1102  -> ret b1)
                       else fail "intro: unification failed"))
       | None  ->
           let uu____1110 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1110)
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
           let uu____1129 =
             let uu____1131 = FStar_List.map tr s in
             FStar_List.flatten uu____1131 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1129 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___91_1137 = goal in
            { context = (uu___91_1137.context); witness = w; goal_ty = t }))
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
       let uu____1149 = istrivial goal.context goal.goal_ty in
       if uu____1149
       then
         let t_unit1 = FStar_TypeChecker_Common.t_unit in
         (solve goal t_unit1; dismiss)
       else
         (let uu____1156 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1156))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1163 =
           try
             let uu____1177 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1177
           with
           | e ->
               let uu____1190 = FStar_Syntax_Print.term_to_string t in
               let uu____1191 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1190
                 uu____1191 in
         bind uu____1163
           (fun uu____1198  ->
              match uu____1198 with
              | (t1,typ,guard) ->
                  let uu____1206 =
                    let uu____1207 =
                      let uu____1208 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1208 in
                    Prims.op_Negation uu____1207 in
                  if uu____1206
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1211 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1211
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1215 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1216 =
                          let uu____1217 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1217 in
                        let uu____1218 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1215 uu____1216 uu____1218))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1225 =
           try
             let uu____1239 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1239
           with
           | e ->
               let uu____1252 = FStar_Syntax_Print.term_to_string t in
               let uu____1253 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1252
                 uu____1253 in
         bind uu____1225
           (fun uu____1260  ->
              match uu____1260 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1273 =
                       let uu____1274 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1274 in
                     if uu____1273
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1277 =
                          let uu____1284 =
                            let uu____1290 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1290.FStar_Syntax_Syntax.effect_args in
                          match uu____1284 with
                          | pre::post::uu____1299 -> ((fst pre), (fst post))
                          | uu____1329 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1277 with
                        | (pre,post) ->
                            let uu____1352 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1352
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1355  ->
                                    let uu____1356 =
                                      let uu____1358 =
                                        mk_irrelevant goal.context pre in
                                      [uu____1358] in
                                    add_goals uu____1356))
                            else
                              (let uu____1360 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1361 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1362 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1360 uu____1361 uu____1362)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1371 =
          let uu____1375 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1375 in
        FStar_List.map FStar_Pervasives.fst uu____1371 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1398 = let uu____1401 = exact tm in trytac uu____1401 in
           bind uu____1398
             (fun r  ->
                match r with
                | Some r1 -> ret ()
                | None  ->
                    let uu____1408 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1408 with
                     | (tm1,typ,guard) ->
                         let uu____1416 =
                           let uu____1417 =
                             let uu____1418 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1418 in
                           Prims.op_Negation uu____1417 in
                         if uu____1416
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1421 = arrow_one typ in
                            match uu____1421 with
                            | None  ->
                                let uu____1428 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1428
                            | Some ((bv,aq),uu____1431) ->
                                let uu____1438 =
                                  FStar_TypeChecker_Util.new_implicit_var
                                    "apply"
                                    (goal.goal_ty).FStar_Syntax_Syntax.pos
                                    goal.context bv.FStar_Syntax_Syntax.sort in
                                (match uu____1438 with
                                 | (u,uu____1447,g_u) ->
                                     let tm' =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1
                                         [(u, aq)] None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let uu____1464 = __apply uopt tm' in
                                     bind uu____1464
                                       (fun uu____1466  ->
                                          let uu____1467 =
                                            let uu____1468 =
                                              let uu____1471 =
                                                let uu____1472 =
                                                  FStar_Syntax_Util.head_and_args
                                                    u in
                                                fst uu____1472 in
                                              FStar_Syntax_Subst.compress
                                                uu____1471 in
                                            uu____1468.FStar_Syntax_Syntax.n in
                                          match uu____1467 with
                                          | FStar_Syntax_Syntax.Tm_uvar
                                              (uvar,uu____1491) ->
                                              let uu____1504 =
                                                add_implicits
                                                  g_u.FStar_TypeChecker_Env.implicits in
                                              bind uu____1504
                                                (fun uu____1506  ->
                                                   bind get
                                                     (fun ps  ->
                                                        let uu____1508 =
                                                          uopt &&
                                                            (uvar_free uvar
                                                               ps) in
                                                        if uu____1508
                                                        then ret ()
                                                        else
                                                          (let uu____1511 =
                                                             let uu____1513 =
                                                               let uu____1514
                                                                 =
                                                                 bnorm
                                                                   goal.context
                                                                   u in
                                                               let uu____1515
                                                                 =
                                                                 bnorm
                                                                   goal.context
                                                                   bv.FStar_Syntax_Syntax.sort in
                                                               {
                                                                 context =
                                                                   (goal.context);
                                                                 witness =
                                                                   uu____1514;
                                                                 goal_ty =
                                                                   uu____1515
                                                               } in
                                                             [uu____1513] in
                                                           add_goals
                                                             uu____1511)))
                                          | uu____1516 -> ret ()))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1522 = __apply true tm in focus_cur_goal uu____1522
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1530 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1530 with
         | (tm1,t,guard) ->
             let uu____1538 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1538 with
              | (bs,comp) ->
                  let uu____1553 =
                    FStar_List.fold_left
                      (fun uu____1570  ->
                         fun uu____1571  ->
                           match (uu____1570, uu____1571) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1620 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply_lemma"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1620 with
                                | (u,uu____1635,g_u) ->
                                    let uu____1643 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1643,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1553 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let uu____1675 =
                         let uu____1682 =
                           let uu____1688 =
                             FStar_Syntax_Util.comp_to_comp_typ comp1 in
                           uu____1688.FStar_Syntax_Syntax.effect_args in
                         match uu____1682 with
                         | pre::post::uu____1697 -> ((fst pre), (fst post))
                         | uu____1727 ->
                             failwith "apply_lemma: impossible: not a lemma" in
                       (match uu____1675 with
                        | (pre,post) ->
                            let uu____1750 =
                              let uu____1752 =
                                FStar_Syntax_Util.mk_squash post in
                              FStar_TypeChecker_Rel.try_teq false
                                goal.context uu____1752 goal.goal_ty in
                            (match uu____1750 with
                             | None  ->
                                 let uu____1754 =
                                   let uu____1755 =
                                     FStar_Syntax_Util.mk_squash post in
                                   FStar_Syntax_Print.term_to_string
                                     uu____1755 in
                                 let uu____1756 =
                                   FStar_Syntax_Print.term_to_string
                                     goal.goal_ty in
                                 fail2
                                   "apply_lemma: does not unify with goal: %s vs %s"
                                   uu____1754 uu____1756
                             | Some g ->
                                 let g1 =
                                   let uu____1759 =
                                     FStar_TypeChecker_Rel.solve_deferred_constraints
                                       goal.context g in
                                   FStar_All.pipe_right uu____1759
                                     FStar_TypeChecker_Rel.resolve_implicits in
                                 let solution =
                                   FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                     None
                                     (goal.context).FStar_TypeChecker_Env.range in
                                 let implicits1 =
                                   FStar_All.pipe_right
                                     implicits.FStar_TypeChecker_Env.implicits
                                     (FStar_List.filter
                                        (fun uu____1793  ->
                                           match uu____1793 with
                                           | (uu____1800,uu____1801,uu____1802,tm2,uu____1804,uu____1805)
                                               ->
                                               let uu____1806 =
                                                 FStar_Syntax_Util.head_and_args
                                                   tm2 in
                                               (match uu____1806 with
                                                | (hd1,uu____1817) ->
                                                    let uu____1832 =
                                                      let uu____1833 =
                                                        FStar_Syntax_Subst.compress
                                                          hd1 in
                                                      uu____1833.FStar_Syntax_Syntax.n in
                                                    (match uu____1832 with
                                                     | FStar_Syntax_Syntax.Tm_uvar
                                                         uu____1836 -> true
                                                     | uu____1845 -> false)))) in
                                 (solve goal solution;
                                  (let is_free_uvar uv t1 =
                                     let free_uvars =
                                       let uu____1856 =
                                         let uu____1860 =
                                           FStar_Syntax_Free.uvars t1 in
                                         FStar_Util.set_elements uu____1860 in
                                       FStar_List.map FStar_Pervasives.fst
                                         uu____1856 in
                                     FStar_List.existsML
                                       (fun u  ->
                                          FStar_Syntax_Unionfind.equiv u uv)
                                       free_uvars in
                                   let appears uv goals =
                                     FStar_List.existsML
                                       (fun g'  -> is_free_uvar uv g'.goal_ty)
                                       goals in
                                   let checkone t1 goals =
                                     let uu____1888 =
                                       FStar_Syntax_Util.head_and_args t1 in
                                     match uu____1888 with
                                     | (hd1,uu____1899) ->
                                         (match hd1.FStar_Syntax_Syntax.n
                                          with
                                          | FStar_Syntax_Syntax.Tm_uvar
                                              (uv,uu____1915) ->
                                              appears uv goals
                                          | uu____1928 -> false) in
                                   let sub_goals =
                                     FStar_All.pipe_right implicits1
                                       (FStar_List.map
                                          (fun uu____1945  ->
                                             match uu____1945 with
                                             | (_msg,_env,_uvar,term,typ,uu____1957)
                                                 ->
                                                 let uu____1958 =
                                                   bnorm goal.context term in
                                                 let uu____1959 =
                                                   bnorm goal.context typ in
                                                 {
                                                   context = (goal.context);
                                                   witness = uu____1958;
                                                   goal_ty = uu____1959
                                                 })) in
                                   let rec filter' f xs =
                                     match xs with
                                     | [] -> []
                                     | x::xs1 ->
                                         let uu____1991 = f x xs1 in
                                         if uu____1991
                                         then
                                           let uu____1993 = filter' f xs1 in
                                           x :: uu____1993
                                         else filter' f xs1 in
                                   let sub_goals1 =
                                     filter'
                                       (fun g2  ->
                                          fun goals  ->
                                            let uu____2001 =
                                              checkone g2.witness goals in
                                            Prims.op_Negation uu____2001)
                                       sub_goals in
                                   let pregoal =
                                     mk_irrelevant goal.context pre in
                                   let sub_goals2 =
                                     let uu____2005 =
                                       istrivial goal.context pregoal.goal_ty in
                                     if uu____2005
                                     then sub_goals1
                                     else pregoal :: sub_goals1 in
                                   let uu____2008 =
                                     add_implicits
                                       g1.FStar_TypeChecker_Env.implicits in
                                   bind uu____2008
                                     (fun uu____2010  ->
                                        bind dismiss
                                          (fun uu____2011  ->
                                             add_goals sub_goals2)))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2018 =
           FStar_All.pipe_left mlog
             (fun uu____2023  ->
                let uu____2024 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2025 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2024
                  uu____2025) in
         bind uu____2018
           (fun uu____2026  ->
              let uu____2027 =
                let uu____2029 =
                  let uu____2030 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2030 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2029 in
              match uu____2027 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2037::(x,uu____2039)::(e,uu____2041)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2075 =
                    let uu____2076 = FStar_Syntax_Subst.compress x in
                    uu____2076.FStar_Syntax_Syntax.n in
                  (match uu____2075 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___96_2082 = goal in
                         let uu____2083 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2086 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___96_2082.context);
                           witness = uu____2083;
                           goal_ty = uu____2086
                         } in
                       replace_cur goal1
                   | uu____2089 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2090 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2094 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2094 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2109 = FStar_Util.set_mem x fns_ty in
           if uu____2109
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2112 =
                FStar_TypeChecker_Util.new_implicit_var "clear"
                  (goal.goal_ty).FStar_Syntax_Syntax.pos env' goal.goal_ty in
              match uu____2112 with
              | (u,uu____2121,g) ->
                  let uu____2129 =
                    let uu____2130 =
                      FStar_TypeChecker_Rel.teq_nosmt goal.context
                        goal.witness u in
                    Prims.op_Negation uu____2130 in
                  if uu____2129
                  then fail "clear: unification failed"
                  else
                    (let new_goal =
                       let uu___97_2134 = goal in
                       let uu____2135 = bnorm env' u in
                       {
                         context = env';
                         witness = uu____2135;
                         goal_ty = (uu___97_2134.goal_ty)
                       } in
                     bind dismiss (fun uu____2136  -> add_goals [new_goal]))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2143 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2143 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2158 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2158 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2172 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2172 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___98_2195 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2202 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2202 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2214 = FStar_Syntax_Print.bv_to_string x in
               let uu____2215 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2214 uu____2215
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2228 = revert_all_hd xs1 in
        bind uu____2228 (fun uu____2230  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___99_2240 = g in
           {
             context = ctx';
             witness = (uu___99_2240.witness);
             goal_ty = (uu___99_2240.goal_ty)
           } in
         bind dismiss (fun uu____2241  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___100_2251 = g in
           {
             context = ctx';
             witness = (uu___100_2251.witness);
             goal_ty = (uu___100_2251.goal_ty)
           } in
         bind dismiss (fun uu____2252  -> add_goals [g']))
let rec bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2273 = FStar_Syntax_Subst.compress t in
          uu____2273.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2296 =
                let uu____2306 = ff hd1 in
                let uu____2307 =
                  FStar_List.map
                    (fun uu____2315  ->
                       match uu____2315 with
                       | (a,q) -> let uu____2322 = ff a in (uu____2322, q))
                    args in
                (uu____2306, uu____2307) in
              FStar_Syntax_Syntax.Tm_app uu____2296
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2351 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2351 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2357 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2357 t' in
                   let uu____2358 =
                     let uu____2373 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2373, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2358)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2392 -> tn in
        f env
          (let uu___101_2393 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___101_2393.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos =
               (uu___101_2393.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___101_2393.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2427 = f x in
      bind uu____2427
        (fun y  ->
           let uu____2431 = mapM f xs in
           bind uu____2431 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2463 = FStar_Syntax_Subst.compress t in
          uu____2463.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2489 = ff hd1 in
              bind uu____2489
                (fun hd2  ->
                   let fa uu____2500 =
                     match uu____2500 with
                     | (a,q) ->
                         let uu____2508 = ff a in
                         bind uu____2508 (fun a1  -> ret (a1, q)) in
                   let uu____2515 = mapM fa args in
                   bind uu____2515
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2559 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2559 with
               | (bs1,t') ->
                   let uu____2565 =
                     let uu____2567 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2567 t' in
                   bind uu____2565
                     (fun t''  ->
                        let uu____2569 =
                          let uu____2570 =
                            let uu____2585 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2585, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2570 in
                        ret uu____2569))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2604 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___102_2606 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___102_2606.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___102_2606.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___102_2606.FStar_Syntax_Syntax.vars)
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
          let uu____2627 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2627 with
          | (t1,lcomp,g) ->
              let uu____2635 =
                (let uu____2636 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2636) ||
                  (let uu____2637 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2637) in
              if uu____2635
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2643 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env typ in
                 match uu____2643 with
                 | (ut,uvs,guard) ->
                     (log ps
                        (fun uu____2661  ->
                           let uu____2662 =
                             FStar_Syntax_Print.term_to_string t1 in
                           let uu____2663 =
                             FStar_Syntax_Print.term_to_string ut in
                           FStar_Util.print2
                             "Pointwise_rec: making equality %s = %s\n"
                             uu____2662 uu____2663);
                      (let g' =
                         let uu____2665 =
                           let uu____2666 =
                             FStar_TypeChecker_TcTerm.universe_of env typ in
                           FStar_Syntax_Util.mk_eq2 uu____2666 typ t1 ut in
                         mk_irrelevant env uu____2665 in
                       let uu____2667 = add_goals [g'] in
                       bind uu____2667
                         (fun uu____2669  ->
                            let uu____2670 =
                              bind tau
                                (fun uu____2672  ->
                                   let guard1 =
                                     let uu____2674 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env guard in
                                     FStar_All.pipe_right uu____2674
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env guard1;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.WHNF]
                                        env ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2670))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2685 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2685 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2706  ->
                   let uu____2707 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2707);
              bind dismiss_all
                (fun uu____2708  ->
                   let uu____2709 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2709
                     (fun gt'  ->
                        log ps
                          (fun uu____2713  ->
                             let uu____2714 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2714);
                        (let uu____2715 = push_goals gs in
                         bind uu____2715
                           (fun uu____2717  ->
                              add_goals
                                [(let uu___103_2718 = g in
                                  {
                                    context = (uu___103_2718.context);
                                    witness = (uu___103_2718.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2721 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2721 with
       | Some t ->
           let uu____2731 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2731 with
            | (hd1,args) ->
                let uu____2752 =
                  let uu____2760 =
                    let uu____2761 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2761.FStar_Syntax_Syntax.n in
                  (uu____2760, args) in
                (match uu____2752 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2771::(l,uu____2773)::(r,uu____2775)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.eq2_lid
                     ->
                     let uu____2809 =
                       let uu____2810 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____2810 in
                     if uu____2809
                     then
                       let uu____2812 = FStar_Syntax_Print.term_to_string l in
                       let uu____2813 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____2812 uu____2813
                     else
                       (let t_unit1 = FStar_TypeChecker_Common.t_unit in
                        solve g t_unit1; dismiss)
                 | (hd2,uu____2820) ->
                     let uu____2831 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____2831))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___104_2841 = ps in
              {
                main_context = (uu___104_2841.main_context);
                main_goal = (uu___104_2841.main_goal);
                all_implicits = (uu___104_2841.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___104_2841.smt_goals)
              })
       | uu____2842 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___105_2850 = ps in
              {
                main_context = (uu___105_2850.main_context);
                main_goal = (uu___105_2850.main_goal);
                all_implicits = (uu___105_2850.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___105_2850.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2854 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2868 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2868 with
         | (t1,typ,guard) ->
             let uu____2878 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2878 with
              | (hd1,args) ->
                  let uu____2907 =
                    let uu____2915 =
                      let uu____2916 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2916.FStar_Syntax_Syntax.n in
                    (uu____2915, args) in
                  (match uu____2907 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2929)::(q,uu____2931)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___106_2960 = g in
                         let uu____2961 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2961;
                           witness = (uu___106_2960.witness);
                           goal_ty = (uu___106_2960.goal_ty)
                         } in
                       let g2 =
                         let uu___107_2963 = g in
                         let uu____2964 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2964;
                           witness = (uu___107_2963.witness);
                           goal_ty = (uu___107_2963.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____2967  ->
                            let uu____2968 = add_goals [g1; g2] in
                            bind uu____2968
                              (fun uu____2972  ->
                                 let uu____2973 =
                                   let uu____2976 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____2977 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____2976, uu____2977) in
                                 ret uu____2973))
                   | uu____2980 ->
                       let uu____2988 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____2988)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2994 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2998 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____3002 -> false
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
      let uu____3022 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____3022 with
      | (u,uu____3030,g_u) ->
          let g = { context = env; witness = u; goal_ty = typ } in
          {
            main_context = env;
            main_goal = g;
            all_implicits = [];
            goals = [g];
            smt_goals = []
          }