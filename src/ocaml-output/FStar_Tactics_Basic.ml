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
      (let uu____394 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____394);
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
      let uu____434 = FStar_ST.read tac_verb_dbg in
      match uu____434 with
      | None  ->
          ((let uu____440 =
              let uu____442 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              Some uu____442 in
            FStar_ST.write tac_verb_dbg uu____440);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____468 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____468
        then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
        else ());
       Failed (msg, ps))
let fail1 msg x = let uu____483 = FStar_Util.format1 msg x in fail uu____483
let fail2 msg x y =
  let uu____502 = FStar_Util.format2 msg x y in fail uu____502
let fail3 msg x y z =
  let uu____526 = FStar_Util.format3 msg x y z in fail uu____526
let trytac t =
  mk_tac
    (fun ps  ->
       let tx = FStar_Syntax_Unionfind.new_transaction () in
       let uu____541 = run t ps in
       match uu____541 with
       | Success (a,q) ->
           (FStar_Syntax_Unionfind.commit tx; Success ((Some a), q))
       | Failed (uu____550,uu____551) ->
           (FStar_Syntax_Unionfind.rollback tx; Success (None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____560  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____567 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____567
      then ()
      else
        (let uu____569 =
           let uu____570 =
             let uu____571 = FStar_Syntax_Print.term_to_string solution in
             let uu____572 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____573 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____571
               uu____572 uu____573 in
           TacFailure uu____570 in
         raise uu____569)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____576 =
         let uu___78_577 = p in
         let uu____578 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_577.main_context);
           main_goal = (uu___78_577.main_goal);
           all_implicits = (uu___78_577.all_implicits);
           goals = uu____578;
           smt_goals = (uu___78_577.smt_goals)
         } in
       set uu____576)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_582 = p in
          {
            main_context = (uu___79_582.main_context);
            main_goal = (uu___79_582.main_goal);
            all_implicits = (uu___79_582.all_implicits);
            goals = [];
            smt_goals = (uu___79_582.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_591 = p in
            {
              main_context = (uu___80_591.main_context);
              main_goal = (uu___80_591.main_goal);
              all_implicits = (uu___80_591.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_591.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_600 = p in
            {
              main_context = (uu___81_600.main_context);
              main_goal = (uu___81_600.main_goal);
              all_implicits = (uu___81_600.all_implicits);
              goals = (uu___81_600.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_609 = p in
            {
              main_context = (uu___82_609.main_context);
              main_goal = (uu___82_609.main_goal);
              all_implicits = (uu___82_609.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___82_609.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_618 = p in
            {
              main_context = (uu___83_618.main_context);
              main_goal = (uu___83_618.main_goal);
              all_implicits = (uu___83_618.all_implicits);
              goals = (uu___83_618.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____624  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_631 = p in
            {
              main_context = (uu___84_631.main_context);
              main_goal = (uu___84_631.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_631.goals);
              smt_goals = (uu___84_631.smt_goals)
            }))
let add_irrelevant_goal: env -> FStar_Syntax_Syntax.typ -> Prims.unit tac =
  fun env  ->
    fun phi  ->
      let typ = FStar_Syntax_Util.mk_squash phi in
      let uu____649 =
        FStar_TypeChecker_Util.new_implicit_var "add_irrelevant_goal"
          phi.FStar_Syntax_Syntax.pos env typ in
      match uu____649 with
      | (u,uu____658,g_u) ->
          let goal = { context = env; witness = u; goal_ty = typ } in
          let uu____667 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____667 (fun uu____669  -> add_goals [goal])
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____673 = FStar_Syntax_Util.un_squash t in
    match uu____673 with
    | Some t' ->
        let uu____682 =
          let uu____683 = FStar_Syntax_Subst.compress t' in
          uu____683.FStar_Syntax_Syntax.n in
        (match uu____682 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____687 -> false)
    | uu____688 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____695 = FStar_Syntax_Util.un_squash t in
    match uu____695 with
    | Some t' ->
        let uu____704 =
          let uu____705 = FStar_Syntax_Subst.compress t' in
          uu____705.FStar_Syntax_Syntax.n in
        (match uu____704 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____709 -> false)
    | uu____710 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____722 = is_irrelevant g in
       if uu____722
       then bind dismiss (fun uu____724  -> add_smt_goals [g])
       else
         (let uu____726 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____726))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____756 =
         try let uu____773 = FStar_List.splitAt n1 p.goals in ret uu____773
         with | uu____788 -> fail "divide: not enough goals" in
       bind uu____756
         (fun uu____799  ->
            match uu____799 with
            | (lgs,rgs) ->
                let lp =
                  let uu___85_814 = p in
                  {
                    main_context = (uu___85_814.main_context);
                    main_goal = (uu___85_814.main_goal);
                    all_implicits = (uu___85_814.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___86_816 = p in
                  {
                    main_context = (uu___86_816.main_context);
                    main_goal = (uu___86_816.main_goal);
                    all_implicits = (uu___86_816.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____817 = set lp in
                bind uu____817
                  (fun uu____821  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____828 = set rp in
                               bind uu____828
                                 (fun uu____832  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___87_840 = p in
                                                {
                                                  main_context =
                                                    (uu___87_840.main_context);
                                                  main_goal =
                                                    (uu___87_840.main_goal);
                                                  all_implicits =
                                                    (uu___87_840.all_implicits);
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
                                              let uu____841 = set p' in
                                              bind uu____841
                                                (fun uu____845  -> ret (a, b))))))))))
let focus_cur_goal f =
  let uu____858 = divide (Prims.parse_int "1") f idtac in
  bind uu____858 (fun uu____864  -> match uu____864 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____885::uu____886 ->
           let uu____888 =
             let uu____893 = map tau in
             divide (Prims.parse_int "1") tau uu____893 in
           bind uu____888
             (fun uu____901  -> match uu____901 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____924 =
        bind t1
          (fun uu____926  ->
             let uu____927 = map t2 in
             bind uu____927 (fun uu____931  -> ret ())) in
      focus_cur_goal uu____924
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____939 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____939 with
       | Some (b,c) ->
           let uu____950 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____950 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____970 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____973 =
                  let uu____974 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____974 in
                if uu____973
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____987 =
                     FStar_TypeChecker_Util.new_implicit_var "intro"
                       typ'.FStar_Syntax_Syntax.pos env' typ' in
                   match uu____987 with
                   | (u,uu____998,g) ->
                       let uu____1006 =
                         let uu____1007 = FStar_Syntax_Util.abs [b1] u None in
                         FStar_TypeChecker_Rel.teq_nosmt goal.context
                           goal.witness uu____1007 in
                       if uu____1006
                       then
                         let g1 =
                           let uu____1021 =
                             FStar_TypeChecker_Rel.solve_deferred_constraints
                               goal.context g in
                           FStar_All.pipe_right uu____1021
                             FStar_TypeChecker_Rel.resolve_implicits in
                         let uu____1022 =
                           add_implicits g1.FStar_TypeChecker_Env.implicits in
                         bind uu____1022
                           (fun uu____1026  ->
                              let uu____1027 =
                                let uu____1029 =
                                  let uu___90_1030 = goal in
                                  let uu____1031 = bnorm env' u in
                                  let uu____1032 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1031;
                                    goal_ty = uu____1032
                                  } in
                                replace_cur uu____1029 in
                              bind uu____1027 (fun uu____1035  -> ret b1))
                       else fail "intro: unification failed"))
       | None  ->
           let uu____1043 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1043)
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
           let uu____1062 =
             let uu____1064 = FStar_List.map tr s in
             FStar_List.flatten uu____1064 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1062 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___91_1070 = goal in
            { context = (uu___91_1070.context); witness = w; goal_ty = t }))
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
       let uu____1082 = istrivial goal.context goal.goal_ty in
       if uu____1082
       then (solve goal FStar_Syntax_Const.exp_unit; dismiss)
       else
         (let uu____1086 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1086))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1093 =
           try
             let uu____1107 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1107
           with
           | e ->
               let uu____1120 = FStar_Syntax_Print.term_to_string t in
               let uu____1121 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1120
                 uu____1121 in
         bind uu____1093
           (fun uu____1128  ->
              match uu____1128 with
              | (t1,typ,guard) ->
                  let uu____1136 =
                    let uu____1137 =
                      let uu____1138 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1138 in
                    Prims.op_Negation uu____1137 in
                  if uu____1136
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1141 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1141
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1145 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1146 =
                          let uu____1147 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1147 in
                        let uu____1148 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1145 uu____1146 uu____1148))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1155 =
           try
             let uu____1169 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1169
           with
           | e ->
               let uu____1182 = FStar_Syntax_Print.term_to_string t in
               let uu____1183 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1182
                 uu____1183 in
         bind uu____1155
           (fun uu____1190  ->
              match uu____1190 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1203 =
                       let uu____1204 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1204 in
                     if uu____1203
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1207 =
                          let uu____1214 =
                            let uu____1220 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1220.FStar_Syntax_Syntax.effect_args in
                          match uu____1214 with
                          | pre::post::uu____1229 -> ((fst pre), (fst post))
                          | uu____1259 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1207 with
                        | (pre,post) ->
                            let uu____1282 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1282
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1285  ->
                                    add_irrelevant_goal goal.context pre))
                            else
                              (let uu____1287 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1288 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1289 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1287 uu____1288 uu____1289)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1298 =
          let uu____1302 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1302 in
        FStar_List.map FStar_Pervasives.fst uu____1298 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1325 = let uu____1328 = exact tm in trytac uu____1328 in
           bind uu____1325
             (fun r  ->
                match r with
                | Some r1 -> ret ()
                | None  ->
                    let uu____1335 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1335 with
                     | (tm1,typ,guard) ->
                         let uu____1343 =
                           let uu____1344 =
                             let uu____1345 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1345 in
                           Prims.op_Negation uu____1344 in
                         if uu____1343
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1348 = FStar_Syntax_Util.arrow_one typ in
                            match uu____1348 with
                            | None  ->
                                let uu____1355 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1355
                            | Some ((bv,aq),c) ->
                                let uu____1365 =
                                  let uu____1366 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____1366 in
                                if uu____1365
                                then fail "apply: not total"
                                else
                                  (let uu____1369 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   match uu____1369 with
                                   | (u,uu____1378,g_u) ->
                                       let tm' =
                                         FStar_Syntax_Syntax.mk_Tm_app tm1
                                           [(u, aq)] None
                                           (goal.context).FStar_TypeChecker_Env.range in
                                       let uu____1395 = __apply uopt tm' in
                                       bind uu____1395
                                         (fun uu____1397  ->
                                            let g_u1 =
                                              let uu____1399 =
                                                FStar_TypeChecker_Rel.solve_deferred_constraints
                                                  goal.context g_u in
                                              FStar_All.pipe_right uu____1399
                                                FStar_TypeChecker_Rel.resolve_implicits in
                                            let uu____1400 =
                                              let uu____1401 =
                                                let uu____1404 =
                                                  let uu____1405 =
                                                    FStar_Syntax_Util.head_and_args
                                                      u in
                                                  fst uu____1405 in
                                                FStar_Syntax_Subst.compress
                                                  uu____1404 in
                                              uu____1401.FStar_Syntax_Syntax.n in
                                            match uu____1400 with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                (uvar,uu____1424) ->
                                                let uu____1437 =
                                                  add_implicits
                                                    g_u1.FStar_TypeChecker_Env.implicits in
                                                bind uu____1437
                                                  (fun uu____1439  ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1441 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____1441
                                                          then ret ()
                                                          else
                                                            (let uu____1444 =
                                                               let uu____1446
                                                                 =
                                                                 let uu____1447
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____1448
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1447;
                                                                   goal_ty =
                                                                    uu____1448
                                                                 } in
                                                               [uu____1446] in
                                                             add_goals
                                                               uu____1444)))
                                            | uu____1449 -> ret ()))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1455 = __apply true tm in focus_cur_goal uu____1455
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1463 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1463 with
         | (tm1,t,guard) ->
             let uu____1471 =
               let uu____1472 =
                 let uu____1473 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1473 in
               Prims.op_Negation uu____1472 in
             if uu____1471
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1476 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____1476 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____1493 =
                         FStar_List.fold_left
                           (fun uu____1510  ->
                              fun uu____1511  ->
                                match (uu____1510, uu____1511) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____1560 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____1560 with
                                     | (u,uu____1575,g_u) ->
                                         let uu____1583 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____1583,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____1493 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1615 =
                             let uu____1622 =
                               let uu____1628 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____1628.FStar_Syntax_Syntax.effect_args in
                             match uu____1622 with
                             | pre::post::uu____1637 ->
                                 ((fst pre), (fst post))
                             | uu____1667 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____1615 with
                            | (pre,post) ->
                                let uu____1690 =
                                  let uu____1692 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____1692 goal.goal_ty in
                                (match uu____1690 with
                                 | None  ->
                                     let uu____1694 =
                                       let uu____1695 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____1695 in
                                     let uu____1696 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____1694 uu____1696
                                 | Some g ->
                                     let g1 =
                                       let uu____1699 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1699
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1733  ->
                                               match uu____1733 with
                                               | (uu____1740,uu____1741,uu____1742,tm2,uu____1744,uu____1745)
                                                   ->
                                                   let uu____1746 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1746 with
                                                    | (hd1,uu____1757) ->
                                                        let uu____1772 =
                                                          let uu____1773 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1773.FStar_Syntax_Syntax.n in
                                                        (match uu____1772
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1776 ->
                                                             true
                                                         | uu____1785 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____1787  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____1797 =
                                                 let uu____1801 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____1801 in
                                               FStar_List.map
                                                 FStar_Pervasives.fst
                                                 uu____1797 in
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
                                             let uu____1829 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____1829 with
                                             | (hd1,uu____1840) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____1856) ->
                                                      appears uv goals
                                                  | uu____1869 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____1886  ->
                                                     match uu____1886 with
                                                     | (_msg,_env,_uvar,term,typ,uu____1898)
                                                         ->
                                                         let uu____1899 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____1900 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____1899;
                                                           goal_ty =
                                                             uu____1900
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____1932 = f x xs1 in
                                                 if uu____1932
                                                 then
                                                   let uu____1934 =
                                                     filter' f xs1 in
                                                   x :: uu____1934
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g2  ->
                                                  fun goals  ->
                                                    let uu____1942 =
                                                      checkone g2.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____1942) sub_goals in
                                           let uu____1943 =
                                             add_irrelevant_goal goal.context
                                               pre in
                                           bind uu____1943
                                             (fun uu____1945  ->
                                                let uu____1946 =
                                                  trytac trivial in
                                                bind uu____1946
                                                  (fun uu____1950  ->
                                                     let uu____1952 =
                                                       add_implicits
                                                         g1.FStar_TypeChecker_Env.implicits in
                                                     bind uu____1952
                                                       (fun uu____1954  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____1961 =
           FStar_All.pipe_left mlog
             (fun uu____1966  ->
                let uu____1967 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____1968 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1967
                  uu____1968) in
         bind uu____1961
           (fun uu____1969  ->
              let uu____1970 =
                let uu____1972 =
                  let uu____1973 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____1973 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1972 in
              match uu____1970 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1980::(x,uu____1982)::(e,uu____1984)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2018 =
                    let uu____2019 = FStar_Syntax_Subst.compress x in
                    uu____2019.FStar_Syntax_Syntax.n in
                  (match uu____2018 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___96_2025 = goal in
                         let uu____2026 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2029 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___96_2025.context);
                           witness = uu____2026;
                           goal_ty = uu____2029
                         } in
                       replace_cur goal1
                   | uu____2032 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2033 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2037 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2037 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2052 = FStar_Util.set_mem x fns_ty in
           if uu____2052
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2055 =
                FStar_TypeChecker_Util.new_implicit_var "clear"
                  (goal.goal_ty).FStar_Syntax_Syntax.pos env' goal.goal_ty in
              match uu____2055 with
              | (u,uu____2064,g) ->
                  let uu____2072 =
                    let uu____2073 =
                      FStar_TypeChecker_Rel.teq_nosmt goal.context
                        goal.witness u in
                    Prims.op_Negation uu____2073 in
                  if uu____2072
                  then fail "clear: unification failed"
                  else
                    (let new_goal =
                       let uu___97_2077 = goal in
                       let uu____2078 = bnorm env' u in
                       {
                         context = env';
                         witness = uu____2078;
                         goal_ty = (uu___97_2077.goal_ty)
                       } in
                     let g1 =
                       let uu____2080 =
                         FStar_TypeChecker_Rel.solve_deferred_constraints
                           goal.context g in
                       FStar_All.pipe_right uu____2080
                         FStar_TypeChecker_Rel.resolve_implicits in
                     bind dismiss
                       (fun uu____2081  ->
                          let uu____2082 =
                            add_implicits g1.FStar_TypeChecker_Env.implicits in
                          bind uu____2082
                            (fun uu____2084  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2091 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2091 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2106 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2106 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2120 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2120 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___98_2143 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2150 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2150 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2162 = FStar_Syntax_Print.bv_to_string x in
               let uu____2163 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2162 uu____2163
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2176 = revert_all_hd xs1 in
        bind uu____2176 (fun uu____2178  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___99_2188 = g in
           {
             context = ctx';
             witness = (uu___99_2188.witness);
             goal_ty = (uu___99_2188.goal_ty)
           } in
         bind dismiss (fun uu____2189  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___100_2199 = g in
           {
             context = ctx';
             witness = (uu___100_2199.witness);
             goal_ty = (uu___100_2199.goal_ty)
           } in
         bind dismiss (fun uu____2200  -> add_goals [g']))
let rec bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2221 = FStar_Syntax_Subst.compress t in
          uu____2221.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2244 =
                let uu____2254 = ff hd1 in
                let uu____2255 =
                  FStar_List.map
                    (fun uu____2263  ->
                       match uu____2263 with
                       | (a,q) -> let uu____2270 = ff a in (uu____2270, q))
                    args in
                (uu____2254, uu____2255) in
              FStar_Syntax_Syntax.Tm_app uu____2244
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2299 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2299 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2305 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2305 t' in
                   let uu____2306 =
                     let uu____2321 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2321, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2306)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2340 -> tn in
        f env
          (let uu___101_2341 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___101_2341.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos =
               (uu___101_2341.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___101_2341.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2375 = f x in
      bind uu____2375
        (fun y  ->
           let uu____2379 = mapM f xs in
           bind uu____2379 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2411 = FStar_Syntax_Subst.compress t in
          uu____2411.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2437 = ff hd1 in
              bind uu____2437
                (fun hd2  ->
                   let fa uu____2448 =
                     match uu____2448 with
                     | (a,q) ->
                         let uu____2456 = ff a in
                         bind uu____2456 (fun a1  -> ret (a1, q)) in
                   let uu____2463 = mapM fa args in
                   bind uu____2463
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2507 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2507 with
               | (bs1,t') ->
                   let uu____2513 =
                     let uu____2515 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2515 t' in
                   bind uu____2513
                     (fun t''  ->
                        let uu____2517 =
                          let uu____2518 =
                            let uu____2533 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2533, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2518 in
                        ret uu____2517))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2552 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___102_2554 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___102_2554.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___102_2554.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___102_2554.FStar_Syntax_Syntax.vars)
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
          let uu____2575 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2575 with
          | (t1,lcomp,g) ->
              let uu____2583 =
                (let uu____2584 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2584) ||
                  (let uu____2585 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2585) in
              if uu____2583
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2591 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env typ in
                 match uu____2591 with
                 | (ut,uvs,guard) ->
                     (log ps
                        (fun uu____2609  ->
                           let uu____2610 =
                             FStar_Syntax_Print.term_to_string t1 in
                           let uu____2611 =
                             FStar_Syntax_Print.term_to_string ut in
                           FStar_Util.print2
                             "Pointwise_rec: making equality %s = %s\n"
                             uu____2610 uu____2611);
                      (let uu____2612 =
                         let uu____2614 =
                           let uu____2615 =
                             FStar_TypeChecker_TcTerm.universe_of env typ in
                           FStar_Syntax_Util.mk_eq2 uu____2615 typ t1 ut in
                         add_irrelevant_goal env uu____2614 in
                       bind uu____2612
                         (fun uu____2616  ->
                            let uu____2617 =
                              bind tau
                                (fun uu____2619  ->
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env guard;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                        env ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2617))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2630 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2630 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2651  ->
                   let uu____2652 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2652);
              bind dismiss_all
                (fun uu____2653  ->
                   let uu____2654 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2654
                     (fun gt'  ->
                        log ps
                          (fun uu____2658  ->
                             let uu____2659 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2659);
                        (let uu____2660 = push_goals gs in
                         bind uu____2660
                           (fun uu____2662  ->
                              add_goals
                                [(let uu___103_2663 = g in
                                  {
                                    context = (uu___103_2663.context);
                                    witness = (uu___103_2663.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2666 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2666 with
       | Some t ->
           let uu____2676 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2676 with
            | (hd1,args) ->
                let uu____2697 =
                  let uu____2705 =
                    let uu____2706 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2706.FStar_Syntax_Syntax.n in
                  (uu____2705, args) in
                (match uu____2697 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2716::(l,uu____2718)::(r,uu____2720)::[]) when
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
                     let uu____2756 =
                       let uu____2757 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l1 r1 in
                       Prims.op_Negation uu____2757 in
                     if uu____2756
                     then
                       let uu____2759 = FStar_Syntax_Print.term_to_string l1 in
                       let uu____2760 = FStar_Syntax_Print.term_to_string r1 in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____2759 uu____2760
                     else
                       (let t_unit1 = FStar_TypeChecker_Common.t_unit in
                        solve g t_unit1; dismiss)
                 | (hd2,uu____2767) ->
                     let uu____2778 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____2778))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___104_2788 = ps in
              {
                main_context = (uu___104_2788.main_context);
                main_goal = (uu___104_2788.main_goal);
                all_implicits = (uu___104_2788.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___104_2788.smt_goals)
              })
       | uu____2789 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___105_2797 = ps in
              {
                main_context = (uu___105_2797.main_context);
                main_goal = (uu___105_2797.main_goal);
                all_implicits = (uu___105_2797.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___105_2797.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2801 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2815 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2815 with
         | (t1,typ,guard) ->
             let uu____2825 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2825 with
              | (hd1,args) ->
                  let uu____2854 =
                    let uu____2862 =
                      let uu____2863 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2863.FStar_Syntax_Syntax.n in
                    (uu____2862, args) in
                  (match uu____2854 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2876)::(q,uu____2878)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___106_2907 = g in
                         let uu____2908 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2908;
                           witness = (uu___106_2907.witness);
                           goal_ty = (uu___106_2907.goal_ty)
                         } in
                       let g2 =
                         let uu___107_2910 = g in
                         let uu____2911 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2911;
                           witness = (uu___107_2910.witness);
                           goal_ty = (uu___107_2910.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____2914  ->
                            let uu____2915 = add_goals [g1; g2] in
                            bind uu____2915
                              (fun uu____2919  ->
                                 let uu____2920 =
                                   let uu____2923 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____2924 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____2923, uu____2924) in
                                 ret uu____2920))
                   | uu____2927 ->
                       let uu____2935 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____2935)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2941 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2945 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2949 -> false
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
      let uu____2969 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____2969 with
      | (u,uu____2977,g_u) ->
          let g = { context = env; witness = u; goal_ty = typ } in
          {
            main_context = env;
            main_goal = g;
            all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
            goals = [g];
            smt_goals = []
          }
let cur_env: env tac =
  bind get
    (fun ps  ->
       let uu____2988 =
         let uu____2989 = FStar_List.hd ps.goals in uu____2989.context in
       FStar_All.pipe_left ret uu____2988)
let cur_goal': FStar_Syntax_Syntax.typ tac =
  bind get
    (fun ps  ->
       let uu____2993 =
         let uu____2994 = FStar_List.hd ps.goals in uu____2994.goal_ty in
       FStar_All.pipe_left ret uu____2993)
let cur_witness: FStar_Syntax_Syntax.term tac =
  bind get
    (fun ps  ->
       let uu____2998 =
         let uu____2999 = FStar_List.hd ps.goals in uu____2999.witness in
       FStar_All.pipe_left ret uu____2998)