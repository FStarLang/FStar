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
         let uu___77_705 = p in
         let uu____706 = FStar_List.tl p.goals in
         {
           main_context = (uu___77_705.main_context);
           main_goal = (uu___77_705.main_goal);
           all_implicits = (uu___77_705.all_implicits);
           goals = uu____706;
           smt_goals = (uu___77_705.smt_goals)
         } in
       set uu____704)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___78_710 = p in
          {
            main_context = (uu___78_710.main_context);
            main_goal = (uu___78_710.main_goal);
            all_implicits = (uu___78_710.all_implicits);
            goals = [];
            smt_goals = (uu___78_710.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___79_720 = p in
            {
              main_context = (uu___79_720.main_context);
              main_goal = (uu___79_720.main_goal);
              all_implicits = (uu___79_720.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___79_720.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_730 = p in
            {
              main_context = (uu___80_730.main_context);
              main_goal = (uu___80_730.main_goal);
              all_implicits = (uu___80_730.all_implicits);
              goals = (uu___80_730.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_740 = p in
            {
              main_context = (uu___81_740.main_context);
              main_goal = (uu___81_740.main_goal);
              all_implicits = (uu___81_740.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___81_740.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_750 = p in
            {
              main_context = (uu___82_750.main_context);
              main_goal = (uu___82_750.main_goal);
              all_implicits = (uu___82_750.all_implicits);
              goals = (uu___82_750.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____757  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___83_765 = p in
            {
              main_context = (uu___83_765.main_context);
              main_goal = (uu___83_765.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___83_765.goals);
              smt_goals = (uu___83_765.smt_goals)
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
                  let uu___84_993 = p in
                  {
                    main_context = (uu___84_993.main_context);
                    main_goal = (uu___84_993.main_goal);
                    all_implicits = (uu___84_993.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___85_995 = p in
                  {
                    main_context = (uu___85_995.main_context);
                    main_goal = (uu___85_995.main_goal);
                    all_implicits = (uu___85_995.all_implicits);
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
                                                let uu___86_1019 = p in
                                                {
                                                  main_context =
                                                    (uu___86_1019.main_context);
                                                  main_goal =
                                                    (uu___86_1019.main_goal);
                                                  all_implicits =
                                                    (uu___86_1019.all_implicits);
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
                              let uu____1202 =
                                let uu____1204 =
                                  let uu___89_1205 = goal in
                                  let uu____1206 = bnorm env' u in
                                  let uu____1207 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1206;
                                    goal_ty = uu____1207;
                                    opts = (uu___89_1205.opts)
                                  } in
                                replace_cur uu____1204 in
                              bind uu____1202 (fun uu____1210  -> ret b1)
                            else fail "intro: unification failed")))
       | None  ->
           let uu____1218 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1218)
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
           let uu____1238 =
             let uu____1240 = FStar_List.map tr s in
             FStar_List.flatten uu____1240 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1238 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___90_1246 = goal in
            {
              context = (uu___90_1246.context);
              witness = w;
              goal_ty = t;
              opts = (uu___90_1246.opts)
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
       let uu____1260 = istrivial goal.context goal.goal_ty in
       if uu____1260
       then (solve goal FStar_Syntax_Const.exp_unit; dismiss)
       else
         (let uu____1264 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1264))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1272 =
           try
             let uu____1286 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1286
           with
           | e ->
               let uu____1299 = FStar_Syntax_Print.term_to_string t in
               let uu____1300 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1299
                 uu____1300 in
         bind uu____1272
           (fun uu____1307  ->
              match uu____1307 with
              | (t1,typ,guard) ->
                  let uu____1315 =
                    let uu____1316 =
                      let uu____1317 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1317 in
                    Prims.op_Negation uu____1316 in
                  if uu____1315
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1320 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1320
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1324 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1325 =
                          let uu____1326 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1326 in
                        let uu____1327 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1324 uu____1325 uu____1327))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1335 =
           try
             let uu____1349 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1349
           with
           | e ->
               let uu____1362 = FStar_Syntax_Print.term_to_string t in
               let uu____1363 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1362
                 uu____1363 in
         bind uu____1335
           (fun uu____1370  ->
              match uu____1370 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1383 =
                       let uu____1384 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1384 in
                     if uu____1383
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1387 =
                          let uu____1394 =
                            let uu____1400 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1400.FStar_Syntax_Syntax.effect_args in
                          match uu____1394 with
                          | pre::post::uu____1409 -> ((fst pre), (fst post))
                          | uu____1439 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1387 with
                        | (pre,post) ->
                            let uu____1462 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1462
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1465  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____1467 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1468 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1469 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1467 uu____1468 uu____1469)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1480 =
          let uu____1484 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1484 in
        FStar_List.map FStar_Pervasives.fst uu____1480 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1511 = let uu____1514 = exact tm in trytac uu____1514 in
           bind uu____1511
             (fun r  ->
                match r with
                | Some r1 -> ret ()
                | None  ->
                    let uu____1521 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1521 with
                     | (tm1,typ,guard) ->
                         let uu____1529 =
                           let uu____1530 =
                             let uu____1531 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1531 in
                           Prims.op_Negation uu____1530 in
                         if uu____1529
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1534 = FStar_Syntax_Util.arrow_one typ in
                            match uu____1534 with
                            | None  ->
                                let uu____1541 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1541
                            | Some ((bv,aq),c) ->
                                let uu____1551 =
                                  let uu____1552 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____1552 in
                                if uu____1551
                                then fail "apply: not total"
                                else
                                  (let uu____1555 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____1555
                                     (fun uu____1561  ->
                                        match uu____1561 with
                                        | (u,g_u) ->
                                            let tm' =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                tm1 [(u, aq)] None
                                                (goal.context).FStar_TypeChecker_Env.range in
                                            let uu____1576 = __apply uopt tm' in
                                            bind uu____1576
                                              (fun uu____1578  ->
                                                 let uu____1579 =
                                                   let uu____1580 =
                                                     let uu____1583 =
                                                       let uu____1584 =
                                                         FStar_Syntax_Util.head_and_args
                                                           u in
                                                       fst uu____1584 in
                                                     FStar_Syntax_Subst.compress
                                                       uu____1583 in
                                                   uu____1580.FStar_Syntax_Syntax.n in
                                                 match uu____1579 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     (uvar,uu____1603) ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1617 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____1617
                                                          then ret ()
                                                          else
                                                            (let uu____1620 =
                                                               let uu____1622
                                                                 =
                                                                 let uu____1623
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____1624
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1623;
                                                                   goal_ty =
                                                                    uu____1624;
                                                                   opts =
                                                                    (goal.opts)
                                                                 } in
                                                               [uu____1622] in
                                                             add_goals
                                                               uu____1620))
                                                 | uu____1625 -> ret ())))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1632 = __apply true tm in focus uu____1632
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1641 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1641 with
         | (tm1,t,guard) ->
             let uu____1649 =
               let uu____1650 =
                 let uu____1651 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1651 in
               Prims.op_Negation uu____1650 in
             if uu____1649
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1654 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____1654 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____1671 =
                         FStar_List.fold_left
                           (fun uu____1688  ->
                              fun uu____1689  ->
                                match (uu____1688, uu____1689) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____1738 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____1738 with
                                     | (u,uu____1753,g_u) ->
                                         let uu____1761 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____1761,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____1671 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1793 =
                             let uu____1800 =
                               let uu____1806 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____1806.FStar_Syntax_Syntax.effect_args in
                             match uu____1800 with
                             | pre::post::uu____1815 ->
                                 ((fst pre), (fst post))
                             | uu____1845 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____1793 with
                            | (pre,post) ->
                                let uu____1868 =
                                  let uu____1870 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____1870 goal.goal_ty in
                                (match uu____1868 with
                                 | None  ->
                                     let uu____1872 =
                                       let uu____1873 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____1873 in
                                     let uu____1874 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____1872 uu____1874
                                 | Some g ->
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1909  ->
                                               match uu____1909 with
                                               | (uu____1916,uu____1917,uu____1918,tm2,uu____1920,uu____1921)
                                                   ->
                                                   let uu____1922 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1922 with
                                                    | (hd1,uu____1933) ->
                                                        let uu____1948 =
                                                          let uu____1949 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1949.FStar_Syntax_Syntax.n in
                                                        (match uu____1948
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1952 ->
                                                             true
                                                         | uu____1961 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____1963  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____1973 =
                                                 let uu____1977 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____1977 in
                                               FStar_List.map
                                                 FStar_Pervasives.fst
                                                 uu____1973 in
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
                                             let uu____2005 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____2005 with
                                             | (hd1,uu____2016) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____2032) ->
                                                      appears uv goals
                                                  | uu____2045 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____2062  ->
                                                     match uu____2062 with
                                                     | (_msg,_env,_uvar,term,typ,uu____2074)
                                                         ->
                                                         let uu____2075 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____2076 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____2075;
                                                           goal_ty =
                                                             uu____2076;
                                                           opts = (goal.opts)
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____2108 = f x xs1 in
                                                 if uu____2108
                                                 then
                                                   let uu____2110 =
                                                     filter' f xs1 in
                                                   x :: uu____2110
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____2118 =
                                                      checkone g1.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____2118) sub_goals in
                                           let uu____2119 =
                                             add_irrelevant_goal goal.context
                                               pre goal.opts in
                                           bind uu____2119
                                             (fun uu____2121  ->
                                                let uu____2122 =
                                                  trytac trivial in
                                                bind uu____2122
                                                  (fun uu____2126  ->
                                                     let uu____2128 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits in
                                                     bind uu____2128
                                                       (fun uu____2130  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2138 =
           FStar_All.pipe_left mlog
             (fun uu____2143  ->
                let uu____2144 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2145 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2144
                  uu____2145) in
         bind uu____2138
           (fun uu____2146  ->
              let uu____2147 =
                let uu____2149 =
                  let uu____2150 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2150 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2149 in
              match uu____2147 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2157::(x,uu____2159)::(e,uu____2161)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2195 =
                    let uu____2196 = FStar_Syntax_Subst.compress x in
                    uu____2196.FStar_Syntax_Syntax.n in
                  (match uu____2195 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___95_2202 = goal in
                         let uu____2203 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2206 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___95_2202.context);
                           witness = uu____2203;
                           goal_ty = uu____2206;
                           opts = (uu___95_2202.opts)
                         } in
                       replace_cur goal1
                   | uu____2209 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2210 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2214 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2214 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2229 = FStar_Util.set_mem x fns_ty in
           if uu____2229
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2232 = new_uvar env' goal.goal_ty in
              bind uu____2232
                (fun uu____2238  ->
                   match uu____2238 with
                   | (u,g) ->
                       let uu____2244 =
                         let uu____2245 =
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness u in
                         Prims.op_Negation uu____2245 in
                       if uu____2244
                       then fail "clear: unification failed"
                       else
                         (let new_goal =
                            let uu___96_2249 = goal in
                            let uu____2250 = bnorm env' u in
                            {
                              context = env';
                              witness = uu____2250;
                              goal_ty = (uu___96_2249.goal_ty);
                              opts = (uu___96_2249.opts)
                            } in
                          bind dismiss
                            (fun uu____2251  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2259 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2259 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2274 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2274 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2288 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2288 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___97_2311 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___97_2311.opts)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2319 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2319 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2331 = FStar_Syntax_Print.bv_to_string x in
               let uu____2332 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2331 uu____2332
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2346 = revert_all_hd xs1 in
        bind uu____2346 (fun uu____2348  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___98_2359 = g in
           {
             context = ctx';
             witness = (uu___98_2359.witness);
             goal_ty = (uu___98_2359.goal_ty);
             opts = (uu___98_2359.opts)
           } in
         bind dismiss (fun uu____2360  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___99_2371 = g in
           {
             context = ctx';
             witness = (uu___99_2371.witness);
             goal_ty = (uu___99_2371.goal_ty);
             opts = (uu___99_2371.opts)
           } in
         bind dismiss (fun uu____2372  -> add_goals [g']))
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2406 = f x in
      bind uu____2406
        (fun y  ->
           let uu____2410 = mapM f xs in
           bind uu____2410 (fun ys  -> ret (y :: ys)))
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
                            let uu____2567 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____2568 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____2567, uu____2568, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2552 in
                        ret uu____2551))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2587 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___100_2589 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___100_2589.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___100_2589.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___100_2589.FStar_Syntax_Syntax.vars)
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
            let uu____2618 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____2618 with
            | (t1,lcomp,g) ->
                let uu____2626 =
                  (let uu____2627 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____2627) ||
                    (let uu____2628 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____2628) in
                if uu____2626
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____2634 = new_uvar env typ in
                   bind uu____2634
                     (fun uu____2640  ->
                        match uu____2640 with
                        | (ut,guard) ->
                            (log ps
                               (fun uu____2647  ->
                                  let uu____2648 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  let uu____2649 =
                                    FStar_Syntax_Print.term_to_string ut in
                                  FStar_Util.print2
                                    "Pointwise_rec: making equality %s = %s\n"
                                    uu____2648 uu____2649);
                             (let uu____2650 =
                                let uu____2652 =
                                  let uu____2653 =
                                    FStar_TypeChecker_TcTerm.universe_of env
                                      typ in
                                  FStar_Syntax_Util.mk_eq2 uu____2653 typ t1
                                    ut in
                                add_irrelevant_goal env uu____2652 opts in
                              bind uu____2650
                                (fun uu____2654  ->
                                   let uu____2655 =
                                     bind tau
                                       (fun uu____2657  ->
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env guard;
                                          (let ut1 =
                                             FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                               env ut in
                                           ret ut1)) in
                                   focus uu____2655)))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2669 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2669 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2690  ->
                   let uu____2691 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2691);
              bind dismiss_all
                (fun uu____2692  ->
                   let uu____2693 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____2693
                     (fun gt'  ->
                        log ps
                          (fun uu____2697  ->
                             let uu____2698 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2698);
                        (let uu____2699 = push_goals gs in
                         bind uu____2699
                           (fun uu____2701  ->
                              add_goals
                                [(let uu___101_2702 = g in
                                  {
                                    context = (uu___101_2702.context);
                                    witness = (uu___101_2702.witness);
                                    goal_ty = gt';
                                    opts = (uu___101_2702.opts)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2705 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2705 with
       | Some t ->
           let uu____2715 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2715 with
            | (hd1,args) ->
                let uu____2736 =
                  let uu____2744 =
                    let uu____2745 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2745.FStar_Syntax_Syntax.n in
                  (uu____2744, args) in
                (match uu____2736 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2755::(l,uu____2757)::(r,uu____2759)::[]) when
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
                     let uu____2795 =
                       let uu____2796 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l1 r1 in
                       Prims.op_Negation uu____2796 in
                     if uu____2795
                     then
                       let uu____2798 = FStar_Syntax_Print.term_to_string l1 in
                       let uu____2799 = FStar_Syntax_Print.term_to_string r1 in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____2798 uu____2799
                     else (solve g FStar_Syntax_Const.exp_unit; dismiss)
                 | (hd2,uu____2803) ->
                     let uu____2814 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____2814))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___102_2824 = ps in
              {
                main_context = (uu___102_2824.main_context);
                main_goal = (uu___102_2824.main_goal);
                all_implicits = (uu___102_2824.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___102_2824.smt_goals)
              })
       | uu____2825 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___103_2833 = ps in
              {
                main_context = (uu___103_2833.main_context);
                main_goal = (uu___103_2833.main_goal);
                all_implicits = (uu___103_2833.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___103_2833.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2837 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2852 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2852 with
         | (t1,typ,guard) ->
             let uu____2862 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2862 with
              | (hd1,args) ->
                  let uu____2891 =
                    let uu____2899 =
                      let uu____2900 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2900.FStar_Syntax_Syntax.n in
                    (uu____2899, args) in
                  (match uu____2891 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2913)::(q,uu____2915)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___104_2944 = g in
                         let uu____2945 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2945;
                           witness = (uu___104_2944.witness);
                           goal_ty = (uu___104_2944.goal_ty);
                           opts = (uu___104_2944.opts)
                         } in
                       let g2 =
                         let uu___105_2947 = g in
                         let uu____2948 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2948;
                           witness = (uu___105_2947.witness);
                           goal_ty = (uu___105_2947.goal_ty);
                           opts = (uu___105_2947.opts)
                         } in
                       bind dismiss
                         (fun uu____2951  ->
                            let uu____2952 = add_goals [g1; g2] in
                            bind uu____2952
                              (fun uu____2956  ->
                                 let uu____2957 =
                                   let uu____2960 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____2961 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____2960, uu____2961) in
                                 ret uu____2957))
                   | uu____2964 ->
                       let uu____2972 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____2972)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____2984 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____2984);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___106_2990 = g in
                 {
                   context = (uu___106_2990.context);
                   witness = (uu___106_2990.witness);
                   goal_ty = (uu___106_2990.goal_ty);
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
      let uu____3015 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____3015 with
      | (u,uu____3025,g_u) ->
          let g =
            let uu____3034 = FStar_Options.peek () in
            { context = env; witness = u; goal_ty = typ; opts = uu____3034 } in
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            } in
          (ps, u)