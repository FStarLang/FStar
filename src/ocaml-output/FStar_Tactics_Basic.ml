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
  goal_ty: FStar_Syntax_Syntax.typ;
  opts: FStar_Options.optionstate;}
let __proj__Mkgoal__item__context: goal -> env =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} ->
        __fname__context
let __proj__Mkgoal__item__witness: goal -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} ->
        __fname__witness
let __proj__Mkgoal__item__goal_ty: goal -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} ->
        __fname__goal_ty
let __proj__Mkgoal__item__opts: goal -> FStar_Options.optionstate =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} -> __fname__opts
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
  match projectee with | Success _0 -> true | uu____169 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success _0 -> _0
let uu___is_Failed projectee =
  match projectee with | Failed _0 -> true | uu____204 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed _0 -> _0
exception TacFailure of Prims.string
let uu___is_TacFailure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | TacFailure uu____232 -> true | uu____233 -> false
let __proj__TacFailure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | TacFailure uu____241 -> uu____241
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
       let uu____348 = run t1 p in
       match uu____348 with
       | Success (a,q) -> let uu____353 = t2 a in run uu____353 q
       | Failed (msg,q) -> Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____363 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____363
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____364 = FStar_Syntax_Print.term_to_string g.witness in
    let uu____365 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____364 uu____365
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____378 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____378
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____391 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____391
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____408 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____408
let comp_to_typ:
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____414) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____422) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: goal -> Prims.bool =
  fun g  ->
    let uu____434 =
      let uu____438 =
        FStar_TypeChecker_Normalize.unfold_whnf g.context g.goal_ty in
      FStar_Syntax_Util.un_squash uu____438 in
    match uu____434 with | Some t -> true | uu____444 -> false
let dump_goal ps goal =
  let uu____464 = goal_to_string goal in tacprint uu____464
let dump_cur: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____474 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____477 = FStar_List.hd ps.goals in dump_goal ps uu____477))
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____489 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____489);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____498 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____498);
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
      let uu____542 = FStar_ST.read tac_verb_dbg in
      match uu____542 with
      | None  ->
          ((let uu____548 =
              let uu____550 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              Some uu____550 in
            FStar_ST.write tac_verb_dbg uu____548);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____579 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____579
        then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
        else ());
       Failed (msg, ps))
let fail1 msg x = let uu____597 = FStar_Util.format1 msg x in fail uu____597
let fail2 msg x y =
  let uu____620 = FStar_Util.format2 msg x y in fail uu____620
let fail3 msg x y z =
  let uu____649 = FStar_Util.format3 msg x y z in fail uu____649
let trytac t =
  mk_tac
    (fun ps  ->
       let tx = FStar_Syntax_Unionfind.new_transaction () in
       let uu____666 = run t ps in
       match uu____666 with
       | Success (a,q) ->
           (FStar_Syntax_Unionfind.commit tx; Success ((Some a), q))
       | Failed (uu____675,uu____676) ->
           (FStar_Syntax_Unionfind.rollback tx; Success (None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____686  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____695 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____695
      then ()
      else
        (let uu____697 =
           let uu____698 =
             let uu____699 = FStar_Syntax_Print.term_to_string solution in
             let uu____700 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____701 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____699
               uu____700 uu____701 in
           TacFailure uu____698 in
         raise uu____697)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____704 =
         let uu___78_705 = p in
         let uu____706 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_705.main_context);
           main_goal = (uu___78_705.main_goal);
           all_implicits = (uu___78_705.all_implicits);
           goals = uu____706;
           smt_goals = (uu___78_705.smt_goals)
         } in
       set uu____704)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_710 = p in
          {
            main_context = (uu___79_710.main_context);
            main_goal = (uu___79_710.main_goal);
            all_implicits = (uu___79_710.all_implicits);
            goals = [];
            smt_goals = (uu___79_710.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_720 = p in
            {
              main_context = (uu___80_720.main_context);
              main_goal = (uu___80_720.main_goal);
              all_implicits = (uu___80_720.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_720.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_730 = p in
            {
              main_context = (uu___81_730.main_context);
              main_goal = (uu___81_730.main_goal);
              all_implicits = (uu___81_730.all_implicits);
              goals = (uu___81_730.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_740 = p in
            {
              main_context = (uu___82_740.main_context);
              main_goal = (uu___82_740.main_goal);
              all_implicits = (uu___82_740.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___82_740.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_750 = p in
            {
              main_context = (uu___83_750.main_context);
              main_goal = (uu___83_750.main_goal);
              all_implicits = (uu___83_750.all_implicits);
              goals = (uu___83_750.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____757  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_765 = p in
            {
              main_context = (uu___84_765.main_context);
              main_goal = (uu___84_765.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_765.goals);
              smt_goals = (uu___84_765.smt_goals)
            }))
let new_uvar:
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term* FStar_TypeChecker_Env.guard_t) tac
  =
  fun env  ->
    fun typ  ->
      let uu____786 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____786 with
      | (u,uu____797,g_u) ->
          let uu____805 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____805 (fun uu____809  -> ret (u, g_u))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____816 = FStar_Syntax_Util.un_squash t in
    match uu____816 with
    | Some t' ->
        let uu____825 =
          let uu____826 = FStar_Syntax_Subst.compress t' in
          uu____826.FStar_Syntax_Syntax.n in
        (match uu____825 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____830 -> false)
    | uu____831 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____839 = FStar_Syntax_Util.un_squash t in
    match uu____839 with
    | Some t' ->
        let uu____848 =
          let uu____849 = FStar_Syntax_Subst.compress t' in
          uu____849.FStar_Syntax_Syntax.n in
        (match uu____848 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____853 -> false)
    | uu____854 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let add_irrelevant_goal:
  env ->
    FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun env  ->
    fun phi  ->
      fun opts  ->
        let typ = FStar_Syntax_Util.mk_squash phi in
        let uu____881 = new_uvar env typ in
        bind uu____881
          (fun uu____887  ->
             match uu____887 with
             | (u,g_u) ->
                 let goal =
                   { context = env; witness = u; goal_ty = typ; opts } in
                 add_goals [goal])
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____896 = is_irrelevant g in
       if uu____896
       then bind dismiss (fun uu____898  -> add_smt_goals [g])
       else
         (let uu____900 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____900))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____935 =
         try let uu____952 = FStar_List.splitAt n1 p.goals in ret uu____952
         with | uu____967 -> fail "divide: not enough goals" in
       bind uu____935
         (fun uu____978  ->
            match uu____978 with
            | (lgs,rgs) ->
                let lp =
                  let uu___85_993 = p in
                  {
                    main_context = (uu___85_993.main_context);
                    main_goal = (uu___85_993.main_goal);
                    all_implicits = (uu___85_993.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___86_995 = p in
                  {
                    main_context = (uu___86_995.main_context);
                    main_goal = (uu___86_995.main_goal);
                    all_implicits = (uu___86_995.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____996 = set lp in
                bind uu____996
                  (fun uu____1000  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____1007 = set rp in
                               bind uu____1007
                                 (fun uu____1011  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___87_1019 = p in
                                                {
                                                  main_context =
                                                    (uu___87_1019.main_context);
                                                  main_goal =
                                                    (uu___87_1019.main_goal);
                                                  all_implicits =
                                                    (uu___87_1019.all_implicits);
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
                                              let uu____1020 = set p' in
                                              bind uu____1020
                                                (fun uu____1024  ->
                                                   ret (a, b))))))))))
let focus f =
  let uu____1039 = divide (Prims.parse_int "1") f idtac in
  bind uu____1039
    (fun uu____1045  -> match uu____1045 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____1068::uu____1069 ->
           let uu____1071 =
             let uu____1076 = map tau in
             divide (Prims.parse_int "1") tau uu____1076 in
           bind uu____1071
             (fun uu____1084  ->
                match uu____1084 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1109 =
        bind t1
          (fun uu____1111  ->
             let uu____1112 = map t2 in
             bind uu____1112 (fun uu____1116  -> ret ())) in
      focus uu____1109
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____1124 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1124 with
       | Some (b,c) ->
           let uu____1135 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1135 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1155 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1158 =
                  let uu____1159 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1159 in
                if uu____1158
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1172 = new_uvar env' typ' in
                   bind uu____1172
                     (fun uu____1180  ->
                        match uu____1180 with
                        | (u,g) ->
                            let uu____1188 =
                              let uu____1189 =
                                FStar_Syntax_Util.abs [b1] u None in
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                goal.witness uu____1189 in
                            if uu____1188
                            then
                              let uu____1197 =
                                let uu____1199 =
                                  let uu___90_1200 = goal in
                                  let uu____1201 = bnorm env' u in
                                  let uu____1202 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1201;
                                    goal_ty = uu____1202;
                                    opts = (uu___90_1200.opts)
                                  } in
                                replace_cur uu____1199 in
                              bind uu____1197 (fun uu____1205  -> ret b1)
                            else fail "intro: unification failed")))
       | None  ->
           let uu____1213 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1213)
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
           let uu____1233 =
             let uu____1235 = FStar_List.map tr s in
             FStar_List.flatten uu____1235 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1233 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___91_1241 = goal in
            {
              context = (uu___91_1241.context);
              witness = w;
              goal_ty = t;
              opts = (uu___91_1241.opts)
            }))
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
       let uu____1255 = istrivial goal.context goal.goal_ty in
       if uu____1255
       then (solve goal FStar_Syntax_Const.exp_unit; dismiss)
       else
         (let uu____1259 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1259))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1267 =
           try
             let uu____1281 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1281
           with
           | e ->
               let uu____1294 = FStar_Syntax_Print.term_to_string t in
               let uu____1295 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1294
                 uu____1295 in
         bind uu____1267
           (fun uu____1302  ->
              match uu____1302 with
              | (t1,typ,guard) ->
                  let uu____1310 =
                    let uu____1311 =
                      let uu____1312 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1312 in
                    Prims.op_Negation uu____1311 in
                  if uu____1310
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1315 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1315
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1319 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1320 =
                          let uu____1321 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1321 in
                        let uu____1322 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1319 uu____1320 uu____1322))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1330 =
           try
             let uu____1344 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1344
           with
           | e ->
               let uu____1357 = FStar_Syntax_Print.term_to_string t in
               let uu____1358 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1357
                 uu____1358 in
         bind uu____1330
           (fun uu____1365  ->
              match uu____1365 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1378 =
                       let uu____1379 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1379 in
                     if uu____1378
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1382 =
                          let uu____1389 =
                            let uu____1395 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1395.FStar_Syntax_Syntax.effect_args in
                          match uu____1389 with
                          | pre::post::uu____1404 -> ((fst pre), (fst post))
                          | uu____1434 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1382 with
                        | (pre,post) ->
                            let uu____1457 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1457
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1460  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____1462 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1463 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1464 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1462 uu____1463 uu____1464)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1475 =
          let uu____1479 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1479 in
        FStar_List.map FStar_Pervasives.fst uu____1475 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1506 = let uu____1509 = exact tm in trytac uu____1509 in
           bind uu____1506
             (fun r  ->
                match r with
                | Some r1 -> ret ()
                | None  ->
                    let uu____1516 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1516 with
                     | (tm1,typ,guard) ->
                         let uu____1524 =
                           let uu____1525 =
                             let uu____1526 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1526 in
                           Prims.op_Negation uu____1525 in
                         if uu____1524
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1529 = FStar_Syntax_Util.arrow_one typ in
                            match uu____1529 with
                            | None  ->
                                let uu____1536 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1536
                            | Some ((bv,aq),c) ->
                                let uu____1546 =
                                  let uu____1547 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____1547 in
                                if uu____1546
                                then fail "apply: not total"
                                else
                                  (let uu____1550 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____1550
                                     (fun uu____1556  ->
                                        match uu____1556 with
                                        | (u,g_u) ->
                                            let tm' =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                tm1 [(u, aq)] None
                                                (goal.context).FStar_TypeChecker_Env.range in
                                            let uu____1571 = __apply uopt tm' in
                                            bind uu____1571
                                              (fun uu____1573  ->
                                                 let uu____1574 =
                                                   let uu____1575 =
                                                     let uu____1578 =
                                                       let uu____1579 =
                                                         FStar_Syntax_Util.head_and_args
                                                           u in
                                                       fst uu____1579 in
                                                     FStar_Syntax_Subst.compress
                                                       uu____1578 in
                                                   uu____1575.FStar_Syntax_Syntax.n in
                                                 match uu____1574 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     (uvar,uu____1598) ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1612 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____1612
                                                          then ret ()
                                                          else
                                                            (let uu____1615 =
                                                               let uu____1617
                                                                 =
                                                                 let uu____1618
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____1619
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1618;
                                                                   goal_ty =
                                                                    uu____1619;
                                                                   opts =
                                                                    (goal.opts)
                                                                 } in
                                                               [uu____1617] in
                                                             add_goals
                                                               uu____1615))
                                                 | uu____1620 -> ret ())))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1627 = __apply true tm in focus uu____1627
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1636 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1636 with
         | (tm1,t,guard) ->
             let uu____1644 =
               let uu____1645 =
                 let uu____1646 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1646 in
               Prims.op_Negation uu____1645 in
             if uu____1644
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1649 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____1649 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____1666 =
                         FStar_List.fold_left
                           (fun uu____1683  ->
                              fun uu____1684  ->
                                match (uu____1683, uu____1684) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____1733 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____1733 with
                                     | (u,uu____1748,g_u) ->
                                         let uu____1756 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____1756,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____1666 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1788 =
                             let uu____1795 =
                               let uu____1801 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____1801.FStar_Syntax_Syntax.effect_args in
                             match uu____1795 with
                             | pre::post::uu____1810 ->
                                 ((fst pre), (fst post))
                             | uu____1840 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____1788 with
                            | (pre,post) ->
                                let uu____1863 =
                                  let uu____1865 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____1865 goal.goal_ty in
                                (match uu____1863 with
                                 | None  ->
                                     let uu____1867 =
                                       let uu____1868 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____1868 in
                                     let uu____1869 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____1867 uu____1869
                                 | Some g ->
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1904  ->
                                               match uu____1904 with
                                               | (uu____1911,uu____1912,uu____1913,tm2,uu____1915,uu____1916)
                                                   ->
                                                   let uu____1917 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1917 with
                                                    | (hd1,uu____1928) ->
                                                        let uu____1943 =
                                                          let uu____1944 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1944.FStar_Syntax_Syntax.n in
                                                        (match uu____1943
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1947 ->
                                                             true
                                                         | uu____1956 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____1958  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____1968 =
                                                 let uu____1972 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____1972 in
                                               FStar_List.map
                                                 FStar_Pervasives.fst
                                                 uu____1968 in
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
                                             let uu____2000 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____2000 with
                                             | (hd1,uu____2011) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____2027) ->
                                                      appears uv goals
                                                  | uu____2040 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____2057  ->
                                                     match uu____2057 with
                                                     | (_msg,_env,_uvar,term,typ,uu____2069)
                                                         ->
                                                         let uu____2070 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____2071 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____2070;
                                                           goal_ty =
                                                             uu____2071;
                                                           opts = (goal.opts)
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____2103 = f x xs1 in
                                                 if uu____2103
                                                 then
                                                   let uu____2105 =
                                                     filter' f xs1 in
                                                   x :: uu____2105
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____2113 =
                                                      checkone g1.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____2113) sub_goals in
                                           let uu____2114 =
                                             add_irrelevant_goal goal.context
                                               pre goal.opts in
                                           bind uu____2114
                                             (fun uu____2116  ->
                                                let uu____2117 =
                                                  trytac trivial in
                                                bind uu____2117
                                                  (fun uu____2121  ->
                                                     let uu____2123 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits in
                                                     bind uu____2123
                                                       (fun uu____2125  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2133 =
           FStar_All.pipe_left mlog
             (fun uu____2138  ->
                let uu____2139 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2140 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2139
                  uu____2140) in
         bind uu____2133
           (fun uu____2141  ->
              let uu____2142 =
                let uu____2144 =
                  let uu____2145 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2145 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2144 in
              match uu____2142 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2152::(x,uu____2154)::(e,uu____2156)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2190 =
                    let uu____2191 = FStar_Syntax_Subst.compress x in
                    uu____2191.FStar_Syntax_Syntax.n in
                  (match uu____2190 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___96_2197 = goal in
                         let uu____2198 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2201 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___96_2197.context);
                           witness = uu____2198;
                           goal_ty = uu____2201;
                           opts = (uu___96_2197.opts)
                         } in
                       replace_cur goal1
                   | uu____2204 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2205 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2209 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2209 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2224 = FStar_Util.set_mem x fns_ty in
           if uu____2224
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2227 = new_uvar env' goal.goal_ty in
              bind uu____2227
                (fun uu____2233  ->
                   match uu____2233 with
                   | (u,g) ->
                       let uu____2239 =
                         let uu____2240 =
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness u in
                         Prims.op_Negation uu____2240 in
                       if uu____2239
                       then fail "clear: unification failed"
                       else
                         (let new_goal =
                            let uu___97_2244 = goal in
                            let uu____2245 = bnorm env' u in
                            {
                              context = env';
                              witness = uu____2245;
                              goal_ty = (uu___97_2244.goal_ty);
                              opts = (uu___97_2244.opts)
                            } in
                          bind dismiss
                            (fun uu____2246  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2254 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2254 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2269 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2269 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2283 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2283 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___98_2301 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___98_2301.opts)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2309 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2309 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2321 = FStar_Syntax_Print.bv_to_string x in
               let uu____2322 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2321 uu____2322
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2336 = revert_all_hd xs1 in
        bind uu____2336 (fun uu____2338  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___99_2349 = g in
           {
             context = ctx';
             witness = (uu___99_2349.witness);
             goal_ty = (uu___99_2349.goal_ty);
             opts = (uu___99_2349.opts)
           } in
         bind dismiss (fun uu____2350  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___100_2361 = g in
           {
             context = ctx';
             witness = (uu___100_2361.witness);
             goal_ty = (uu___100_2361.goal_ty);
             opts = (uu___100_2361.opts)
           } in
         bind dismiss (fun uu____2362  -> add_goals [g']))
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2396 = f x in
      bind uu____2396
        (fun y  ->
           let uu____2400 = mapM f xs in
           bind uu____2400 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2435 = FStar_Syntax_Subst.compress t in
          uu____2435.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2461 = ff hd1 in
              bind uu____2461
                (fun hd2  ->
                   let fa uu____2472 =
                     match uu____2472 with
                     | (a,q) ->
                         let uu____2480 = ff a in
                         bind uu____2480 (fun a1  -> ret (a1, q)) in
                   let uu____2487 = mapM fa args in
                   bind uu____2487
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2521 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2521 with
               | (bs1,t') ->
                   let uu____2527 =
                     let uu____2529 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2529 t' in
                   bind uu____2527
                     (fun t''  ->
                        let uu____2531 =
                          let uu____2532 =
                            let uu____2542 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____2543 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____2542, uu____2543, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2532 in
                        ret uu____2531))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2557 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___101_2559 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___101_2559.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___101_2559.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___101_2559.FStar_Syntax_Syntax.vars)
                }))
let pointwise_rec:
  proofstate ->
    Prims.unit tac ->
      FStar_Options.optionstate ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun env  ->
          fun t  ->
            let uu____2588 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____2588 with
            | (t1,lcomp,g) ->
                let uu____2596 =
                  (let uu____2597 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____2597) ||
                    (let uu____2598 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____2598) in
                if uu____2596
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____2604 = new_uvar env typ in
                   bind uu____2604
                     (fun uu____2610  ->
                        match uu____2610 with
                        | (ut,guard) ->
                            (log ps
                               (fun uu____2617  ->
                                  let uu____2618 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  let uu____2619 =
                                    FStar_Syntax_Print.term_to_string ut in
                                  FStar_Util.print2
                                    "Pointwise_rec: making equality %s = %s\n"
                                    uu____2618 uu____2619);
                             (let uu____2620 =
                                let uu____2622 =
                                  let uu____2623 =
                                    FStar_TypeChecker_TcTerm.universe_of env
                                      typ in
                                  FStar_Syntax_Util.mk_eq2 uu____2623 typ t1
                                    ut in
                                add_irrelevant_goal env uu____2622 opts in
                              bind uu____2620
                                (fun uu____2624  ->
                                   let uu____2625 =
                                     bind tau
                                       (fun uu____2627  ->
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env guard;
                                          (let ut1 =
                                             FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                               env ut in
                                           ret ut1)) in
                                   focus uu____2625)))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2639 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2639 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2660  ->
                   let uu____2661 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2661);
              bind dismiss_all
                (fun uu____2662  ->
                   let uu____2663 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____2663
                     (fun gt'  ->
                        log ps
                          (fun uu____2667  ->
                             let uu____2668 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2668);
                        (let uu____2669 = push_goals gs in
                         bind uu____2669
                           (fun uu____2671  ->
                              add_goals
                                [(let uu___102_2672 = g in
                                  {
                                    context = (uu___102_2672.context);
                                    witness = (uu___102_2672.witness);
                                    goal_ty = gt';
                                    opts = (uu___102_2672.opts)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2675 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2675 with
       | Some t ->
           let uu____2685 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2685 with
            | (hd1,args) ->
                let uu____2706 =
                  let uu____2714 =
                    let uu____2715 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2715.FStar_Syntax_Syntax.n in
                  (uu____2714, args) in
                (match uu____2706 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2725::(l,uu____2727)::(r,uu____2729)::[]) when
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
                     let uu____2765 =
                       let uu____2766 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l1 r1 in
                       Prims.op_Negation uu____2766 in
                     if uu____2765
                     then
                       let uu____2768 = FStar_Syntax_Print.term_to_string l1 in
                       let uu____2769 = FStar_Syntax_Print.term_to_string r1 in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____2768 uu____2769
                     else (solve g FStar_Syntax_Const.exp_unit; dismiss)
                 | (hd2,uu____2773) ->
                     let uu____2784 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____2784))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___103_2794 = ps in
              {
                main_context = (uu___103_2794.main_context);
                main_goal = (uu___103_2794.main_goal);
                all_implicits = (uu___103_2794.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___103_2794.smt_goals)
              })
       | uu____2795 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___104_2803 = ps in
              {
                main_context = (uu___104_2803.main_context);
                main_goal = (uu___104_2803.main_goal);
                all_implicits = (uu___104_2803.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___104_2803.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2807 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2822 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2822 with
         | (t1,typ,guard) ->
             let uu____2832 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2832 with
              | (hd1,args) ->
                  let uu____2861 =
                    let uu____2869 =
                      let uu____2870 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2870.FStar_Syntax_Syntax.n in
                    (uu____2869, args) in
                  (match uu____2861 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2883)::(q,uu____2885)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___105_2914 = g in
                         let uu____2915 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2915;
                           witness = (uu___105_2914.witness);
                           goal_ty = (uu___105_2914.goal_ty);
                           opts = (uu___105_2914.opts)
                         } in
                       let g2 =
                         let uu___106_2917 = g in
                         let uu____2918 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2918;
                           witness = (uu___106_2917.witness);
                           goal_ty = (uu___106_2917.goal_ty);
                           opts = (uu___106_2917.opts)
                         } in
                       bind dismiss
                         (fun uu____2921  ->
                            let uu____2922 = add_goals [g1; g2] in
                            bind uu____2922
                              (fun uu____2926  ->
                                 let uu____2927 =
                                   let uu____2930 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____2931 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____2930, uu____2931) in
                                 ret uu____2927))
                   | uu____2934 ->
                       let uu____2942 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____2942)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____2954 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____2954);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___107_2960 = g in
                 {
                   context = (uu___107_2960.context);
                   witness = (uu___107_2960.witness);
                   goal_ty = (uu___107_2960.goal_ty);
                   opts = opts'
                 } in
               replace_cur g'
           | FStar_Getopt.Error err1 ->
               fail2 "Setting options `%s` failed: %s" s err1
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
let cur_env: env tac =
  bind cur_goal (fun g  -> FStar_All.pipe_left ret g.context)
let cur_goal': FStar_Syntax_Syntax.typ tac =
  bind cur_goal (fun g  -> FStar_All.pipe_left ret g.goal_ty)
let cur_witness: FStar_Syntax_Syntax.term tac =
  bind cur_goal (fun g  -> FStar_All.pipe_left ret g.witness)
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> (proofstate* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      let uu____2985 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____2985 with
      | (u,uu____2995,g_u) ->
          let g =
            let uu____3004 = FStar_Options.peek () in
            { context = env; witness = u; goal_ty = typ; opts = uu____3004 } in
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            } in
          (ps, u)