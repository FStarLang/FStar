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
  match projectee with | Success _0 -> true | uu____156 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success _0 -> _0
let uu___is_Failed projectee =
  match projectee with | Failed _0 -> true | uu____187 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed _0 -> _0
exception TacFailure of Prims.string
let uu___is_TacFailure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | TacFailure uu____212 -> true | uu____213 -> false
let __proj__TacFailure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | TacFailure uu____220 -> uu____220
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
       let uu____313 = run t1 p in
       match uu____313 with
       | Success (a,q) -> let uu____318 = t2 a in run uu____318 q
       | Failed (msg,q) -> Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____327 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____327
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____328 = FStar_Syntax_Print.term_to_string g.witness in
    let uu____329 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____328 uu____329
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____339 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____339
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____349 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____349
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____362 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____362
let comp_to_typ:
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____367) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____375) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: goal -> Prims.bool =
  fun g  ->
    let uu____386 =
      let uu____390 =
        FStar_TypeChecker_Normalize.unfold_whnf g.context g.goal_ty in
      FStar_Syntax_Util.un_squash uu____390 in
    match uu____386 with | Some t -> true | uu____396 -> false
let dump_goal ps goal =
  let uu____413 = goal_to_string goal in tacprint uu____413
let dump_cur: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____421 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____424 = FStar_List.hd ps.goals in dump_goal ps uu____424))
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____434 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____434);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____443 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____443);
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
      let uu____483 = FStar_ST.read tac_verb_dbg in
      match uu____483 with
      | None  ->
          ((let uu____489 =
              let uu____491 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              Some uu____491 in
            FStar_ST.write tac_verb_dbg uu____489);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____517 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____517
        then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
        else ());
       Failed (msg, ps))
let fail1 msg x = let uu____532 = FStar_Util.format1 msg x in fail uu____532
let fail2 msg x y =
  let uu____551 = FStar_Util.format2 msg x y in fail uu____551
let fail3 msg x y z =
  let uu____575 = FStar_Util.format3 msg x y z in fail uu____575
let trytac t =
  mk_tac
    (fun ps  ->
       let tx = FStar_Syntax_Unionfind.new_transaction () in
       let uu____590 = run t ps in
       match uu____590 with
       | Success (a,q) ->
           (FStar_Syntax_Unionfind.commit tx; Success ((Some a), q))
       | Failed (uu____599,uu____600) ->
           (FStar_Syntax_Unionfind.rollback tx; Success (None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____609  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____616 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____616
      then ()
      else
        (let uu____618 =
           let uu____619 =
             let uu____620 = FStar_Syntax_Print.term_to_string solution in
             let uu____621 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____622 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____620
               uu____621 uu____622 in
           TacFailure uu____619 in
         raise uu____618)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____625 =
         let uu___77_626 = p in
         let uu____627 = FStar_List.tl p.goals in
         {
           main_context = (uu___77_626.main_context);
           main_goal = (uu___77_626.main_goal);
           all_implicits = (uu___77_626.all_implicits);
           goals = uu____627;
           smt_goals = (uu___77_626.smt_goals)
         } in
       set uu____625)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___78_631 = p in
          {
            main_context = (uu___78_631.main_context);
            main_goal = (uu___78_631.main_goal);
            all_implicits = (uu___78_631.all_implicits);
            goals = [];
            smt_goals = (uu___78_631.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___79_640 = p in
            {
              main_context = (uu___79_640.main_context);
              main_goal = (uu___79_640.main_goal);
              all_implicits = (uu___79_640.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___79_640.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_649 = p in
            {
              main_context = (uu___80_649.main_context);
              main_goal = (uu___80_649.main_goal);
              all_implicits = (uu___80_649.all_implicits);
              goals = (uu___80_649.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_658 = p in
            {
              main_context = (uu___81_658.main_context);
              main_goal = (uu___81_658.main_goal);
              all_implicits = (uu___81_658.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___81_658.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_667 = p in
            {
              main_context = (uu___82_667.main_context);
              main_goal = (uu___82_667.main_goal);
              all_implicits = (uu___82_667.all_implicits);
              goals = (uu___82_667.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____673  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___83_680 = p in
            {
              main_context = (uu___83_680.main_context);
              main_goal = (uu___83_680.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___83_680.goals);
              smt_goals = (uu___83_680.smt_goals)
            }))
let new_uvar:
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term* FStar_TypeChecker_Env.guard_t) tac
  =
  fun env  ->
    fun typ  ->
      let uu____699 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____699 with
      | (u,uu____710,g_u) ->
          let uu____718 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____718 (fun uu____722  -> ret (u, g_u))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____728 = FStar_Syntax_Util.un_squash t in
    match uu____728 with
    | Some t' ->
        let uu____737 =
          let uu____738 = FStar_Syntax_Subst.compress t' in
          uu____738.FStar_Syntax_Syntax.n in
        (match uu____737 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____742 -> false)
    | uu____743 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____750 = FStar_Syntax_Util.un_squash t in
    match uu____750 with
    | Some t' ->
        let uu____759 =
          let uu____760 = FStar_Syntax_Subst.compress t' in
          uu____760.FStar_Syntax_Syntax.n in
        (match uu____759 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____764 -> false)
    | uu____765 -> false
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
        let uu____789 = new_uvar env typ in
        bind uu____789
          (fun uu____795  ->
             match uu____795 with
             | (u,g_u) ->
                 let goal =
                   { context = env; witness = u; goal_ty = typ; opts } in
                 add_goals [goal])
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____804 = is_irrelevant g in
       if uu____804
       then bind dismiss (fun uu____806  -> add_smt_goals [g])
       else
         (let uu____808 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____808))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____838 =
         try let uu____855 = FStar_List.splitAt n1 p.goals in ret uu____855
         with | uu____870 -> fail "divide: not enough goals" in
       bind uu____838
         (fun uu____881  ->
            match uu____881 with
            | (lgs,rgs) ->
                let lp =
                  let uu___84_896 = p in
                  {
                    main_context = (uu___84_896.main_context);
                    main_goal = (uu___84_896.main_goal);
                    all_implicits = (uu___84_896.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___85_898 = p in
                  {
                    main_context = (uu___85_898.main_context);
                    main_goal = (uu___85_898.main_goal);
                    all_implicits = (uu___85_898.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____899 = set lp in
                bind uu____899
                  (fun uu____903  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____910 = set rp in
                               bind uu____910
                                 (fun uu____914  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___86_922 = p in
                                                {
                                                  main_context =
                                                    (uu___86_922.main_context);
                                                  main_goal =
                                                    (uu___86_922.main_goal);
                                                  all_implicits =
                                                    (uu___86_922.all_implicits);
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
                                              let uu____923 = set p' in
                                              bind uu____923
                                                (fun uu____927  -> ret (a, b))))))))))
let focus f =
  let uu____940 = divide (Prims.parse_int "1") f idtac in
  bind uu____940 (fun uu____946  -> match uu____946 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____967::uu____968 ->
           let uu____970 =
             let uu____975 = map tau in
             divide (Prims.parse_int "1") tau uu____975 in
           bind uu____970
             (fun uu____983  -> match uu____983 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1006 =
        bind t1
          (fun uu____1008  ->
             let uu____1009 = map t2 in
             bind uu____1009 (fun uu____1013  -> ret ())) in
      focus uu____1006
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____1021 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1021 with
       | Some (b,c) ->
           let uu____1032 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1032 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1052 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1055 =
                  let uu____1056 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1056 in
                if uu____1055
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1069 = new_uvar env' typ' in
                   bind uu____1069
                     (fun uu____1077  ->
                        match uu____1077 with
                        | (u,g) ->
                            let uu____1085 =
                              let uu____1086 =
                                FStar_Syntax_Util.abs [b1] u None in
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                goal.witness uu____1086 in
                            if uu____1085
                            then
                              let uu____1099 =
                                let uu____1101 =
                                  let uu___89_1102 = goal in
                                  let uu____1103 = bnorm env' u in
                                  let uu____1104 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1103;
                                    goal_ty = uu____1104;
                                    opts = (uu___89_1102.opts)
                                  } in
                                replace_cur uu____1101 in
                              bind uu____1099 (fun uu____1107  -> ret b1)
                            else fail "intro: unification failed")))
       | None  ->
           let uu____1115 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1115)
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
           let uu____1134 =
             let uu____1136 = FStar_List.map tr s in
             FStar_List.flatten uu____1136 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1134 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___90_1142 = goal in
            {
              context = (uu___90_1142.context);
              witness = w;
              goal_ty = t;
              opts = (uu___90_1142.opts)
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
       let uu____1154 = istrivial goal.context goal.goal_ty in
       if uu____1154
       then (solve goal FStar_Syntax_Const.exp_unit; dismiss)
       else
         (let uu____1158 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1158))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1165 =
           try
             let uu____1179 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1179
           with
           | e ->
               let uu____1192 = FStar_Syntax_Print.term_to_string t in
               let uu____1193 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1192
                 uu____1193 in
         bind uu____1165
           (fun uu____1200  ->
              match uu____1200 with
              | (t1,typ,guard) ->
                  let uu____1208 =
                    let uu____1209 =
                      let uu____1210 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1210 in
                    Prims.op_Negation uu____1209 in
                  if uu____1208
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1213 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1213
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1217 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1218 =
                          let uu____1219 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1219 in
                        let uu____1220 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1217 uu____1218 uu____1220))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1227 =
           try
             let uu____1241 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1241
           with
           | e ->
               let uu____1254 = FStar_Syntax_Print.term_to_string t in
               let uu____1255 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1254
                 uu____1255 in
         bind uu____1227
           (fun uu____1262  ->
              match uu____1262 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1275 =
                       let uu____1276 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1276 in
                     if uu____1275
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1279 =
                          let uu____1286 =
                            let uu____1292 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1292.FStar_Syntax_Syntax.effect_args in
                          match uu____1286 with
                          | pre::post::uu____1301 -> ((fst pre), (fst post))
                          | uu____1331 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1279 with
                        | (pre,post) ->
                            let uu____1354 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1354
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1357  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____1359 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1360 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1361 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1359 uu____1360 uu____1361)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1370 =
          let uu____1374 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1374 in
        FStar_List.map FStar_Pervasives.fst uu____1370 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1397 = let uu____1400 = exact tm in trytac uu____1400 in
           bind uu____1397
             (fun r  ->
                match r with
                | Some r1 -> ret ()
                | None  ->
                    let uu____1407 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1407 with
                     | (tm1,typ,guard) ->
                         let uu____1415 =
                           let uu____1416 =
                             let uu____1417 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1417 in
                           Prims.op_Negation uu____1416 in
                         if uu____1415
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1420 = FStar_Syntax_Util.arrow_one typ in
                            match uu____1420 with
                            | None  ->
                                let uu____1427 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1427
                            | Some ((bv,aq),c) ->
                                let uu____1437 =
                                  let uu____1438 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____1438 in
                                if uu____1437
                                then fail "apply: not total"
                                else
                                  (let uu____1441 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____1441
                                     (fun uu____1447  ->
                                        match uu____1447 with
                                        | (u,g_u) ->
                                            let tm' =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                tm1 [(u, aq)] None
                                                (goal.context).FStar_TypeChecker_Env.range in
                                            let uu____1462 = __apply uopt tm' in
                                            bind uu____1462
                                              (fun uu____1464  ->
                                                 let uu____1465 =
                                                   let uu____1466 =
                                                     let uu____1469 =
                                                       let uu____1470 =
                                                         FStar_Syntax_Util.head_and_args
                                                           u in
                                                       fst uu____1470 in
                                                     FStar_Syntax_Subst.compress
                                                       uu____1469 in
                                                   uu____1466.FStar_Syntax_Syntax.n in
                                                 match uu____1465 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     (uvar,uu____1489) ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1503 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____1503
                                                          then ret ()
                                                          else
                                                            (let uu____1506 =
                                                               let uu____1508
                                                                 =
                                                                 let uu____1509
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____1510
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1509;
                                                                   goal_ty =
                                                                    uu____1510;
                                                                   opts =
                                                                    (goal.opts)
                                                                 } in
                                                               [uu____1508] in
                                                             add_goals
                                                               uu____1506))
                                                 | uu____1511 -> ret ())))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1517 = __apply true tm in focus uu____1517
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1525 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1525 with
         | (tm1,t,guard) ->
             let uu____1533 =
               let uu____1534 =
                 let uu____1535 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1535 in
               Prims.op_Negation uu____1534 in
             if uu____1533
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1538 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____1538 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____1555 =
                         FStar_List.fold_left
                           (fun uu____1572  ->
                              fun uu____1573  ->
                                match (uu____1572, uu____1573) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____1622 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____1622 with
                                     | (u,uu____1637,g_u) ->
                                         let uu____1645 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____1645,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____1555 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1677 =
                             let uu____1684 =
                               let uu____1690 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____1690.FStar_Syntax_Syntax.effect_args in
                             match uu____1684 with
                             | pre::post::uu____1699 ->
                                 ((fst pre), (fst post))
                             | uu____1729 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____1677 with
                            | (pre,post) ->
                                let uu____1752 =
                                  let uu____1754 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____1754 goal.goal_ty in
                                (match uu____1752 with
                                 | None  ->
                                     let uu____1756 =
                                       let uu____1757 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____1757 in
                                     let uu____1758 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____1756 uu____1758
                                 | Some g ->
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
                                                        (match uu____1832
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1836 ->
                                                             true
                                                         | uu____1845 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____1847  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____1857 =
                                                 let uu____1861 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____1861 in
                                               FStar_List.map
                                                 FStar_Pervasives.fst
                                                 uu____1857 in
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
                                             let uu____1889 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____1889 with
                                             | (hd1,uu____1900) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____1916) ->
                                                      appears uv goals
                                                  | uu____1929 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____1946  ->
                                                     match uu____1946 with
                                                     | (_msg,_env,_uvar,term,typ,uu____1958)
                                                         ->
                                                         let uu____1959 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____1960 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____1959;
                                                           goal_ty =
                                                             uu____1960;
                                                           opts = (goal.opts)
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____1992 = f x xs1 in
                                                 if uu____1992
                                                 then
                                                   let uu____1994 =
                                                     filter' f xs1 in
                                                   x :: uu____1994
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____2002 =
                                                      checkone g1.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____2002) sub_goals in
                                           let uu____2003 =
                                             add_irrelevant_goal goal.context
                                               pre goal.opts in
                                           bind uu____2003
                                             (fun uu____2005  ->
                                                let uu____2006 =
                                                  trytac trivial in
                                                bind uu____2006
                                                  (fun uu____2010  ->
                                                     let uu____2012 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits in
                                                     bind uu____2012
                                                       (fun uu____2014  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2021 =
           FStar_All.pipe_left mlog
             (fun uu____2026  ->
                let uu____2027 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2028 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2027
                  uu____2028) in
         bind uu____2021
           (fun uu____2029  ->
              let uu____2030 =
                let uu____2032 =
                  let uu____2033 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2033 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2032 in
              match uu____2030 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2040::(x,uu____2042)::(e,uu____2044)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2078 =
                    let uu____2079 = FStar_Syntax_Subst.compress x in
                    uu____2079.FStar_Syntax_Syntax.n in
                  (match uu____2078 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___95_2085 = goal in
                         let uu____2086 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2089 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___95_2085.context);
                           witness = uu____2086;
                           goal_ty = uu____2089;
                           opts = (uu___95_2085.opts)
                         } in
                       replace_cur goal1
                   | uu____2092 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2093 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2097 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2097 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2112 = FStar_Util.set_mem x fns_ty in
           if uu____2112
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2115 = new_uvar env' goal.goal_ty in
              bind uu____2115
                (fun uu____2121  ->
                   match uu____2121 with
                   | (u,g) ->
                       let uu____2127 =
                         let uu____2128 =
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness u in
                         Prims.op_Negation uu____2128 in
                       if uu____2127
                       then fail "clear: unification failed"
                       else
                         (let new_goal =
                            let uu___96_2132 = goal in
                            let uu____2133 = bnorm env' u in
                            {
                              context = env';
                              witness = uu____2133;
                              goal_ty = (uu___96_2132.goal_ty);
                              opts = (uu___96_2132.opts)
                            } in
                          bind dismiss
                            (fun uu____2134  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2141 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2141 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2156 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2156 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2170 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2170 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___97_2193 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___97_2193.opts)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2200 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2200 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2212 = FStar_Syntax_Print.bv_to_string x in
               let uu____2213 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2212 uu____2213
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2226 = revert_all_hd xs1 in
        bind uu____2226 (fun uu____2228  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___98_2238 = g in
           {
             context = ctx';
             witness = (uu___98_2238.witness);
             goal_ty = (uu___98_2238.goal_ty);
             opts = (uu___98_2238.opts)
           } in
         bind dismiss (fun uu____2239  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___99_2249 = g in
           {
             context = ctx';
             witness = (uu___99_2249.witness);
             goal_ty = (uu___99_2249.goal_ty);
             opts = (uu___99_2249.opts)
           } in
         bind dismiss (fun uu____2250  -> add_goals [g']))
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2280 = f x in
      bind uu____2280
        (fun y  ->
           let uu____2284 = mapM f xs in
           bind uu____2284 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2316 = FStar_Syntax_Subst.compress t in
          uu____2316.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2342 = ff hd1 in
              bind uu____2342
                (fun hd2  ->
                   let fa uu____2353 =
                     match uu____2353 with
                     | (a,q) ->
                         let uu____2361 = ff a in
                         bind uu____2361 (fun a1  -> ret (a1, q)) in
                   let uu____2368 = mapM fa args in
                   bind uu____2368
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2412 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2412 with
               | (bs1,t') ->
                   let uu____2418 =
                     let uu____2420 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2420 t' in
                   bind uu____2418
                     (fun t''  ->
                        let uu____2422 =
                          let uu____2423 =
                            let uu____2438 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____2439 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____2438, uu____2439, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2423 in
                        ret uu____2422))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2458 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___100_2460 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___100_2460.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___100_2460.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___100_2460.FStar_Syntax_Syntax.vars)
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
            let uu____2484 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____2484 with
            | (t1,lcomp,g) ->
                let uu____2492 =
                  (let uu____2493 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____2493) ||
                    (let uu____2494 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____2494) in
                if uu____2492
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____2500 = new_uvar env typ in
                   bind uu____2500
                     (fun uu____2506  ->
                        match uu____2506 with
                        | (ut,guard) ->
                            (log ps
                               (fun uu____2513  ->
                                  let uu____2514 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  let uu____2515 =
                                    FStar_Syntax_Print.term_to_string ut in
                                  FStar_Util.print2
                                    "Pointwise_rec: making equality %s = %s\n"
                                    uu____2514 uu____2515);
                             (let uu____2516 =
                                let uu____2518 =
                                  let uu____2519 =
                                    FStar_TypeChecker_TcTerm.universe_of env
                                      typ in
                                  FStar_Syntax_Util.mk_eq2 uu____2519 typ t1
                                    ut in
                                add_irrelevant_goal env uu____2518 opts in
                              bind uu____2516
                                (fun uu____2520  ->
                                   let uu____2521 =
                                     bind tau
                                       (fun uu____2523  ->
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env guard;
                                          (let ut1 =
                                             FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                               env ut in
                                           ret ut1)) in
                                   focus uu____2521)))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2534 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2534 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2555  ->
                   let uu____2556 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2556);
              bind dismiss_all
                (fun uu____2557  ->
                   let uu____2558 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____2558
                     (fun gt'  ->
                        log ps
                          (fun uu____2562  ->
                             let uu____2563 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2563);
                        (let uu____2564 = push_goals gs in
                         bind uu____2564
                           (fun uu____2566  ->
                              add_goals
                                [(let uu___101_2567 = g in
                                  {
                                    context = (uu___101_2567.context);
                                    witness = (uu___101_2567.witness);
                                    goal_ty = gt';
                                    opts = (uu___101_2567.opts)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2570 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2570 with
       | Some t ->
           let uu____2580 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2580 with
            | (hd1,args) ->
                let uu____2601 =
                  let uu____2609 =
                    let uu____2610 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2610.FStar_Syntax_Syntax.n in
                  (uu____2609, args) in
                (match uu____2601 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2620::(l,uu____2622)::(r,uu____2624)::[]) when
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
                     let uu____2660 =
                       let uu____2661 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l1 r1 in
                       Prims.op_Negation uu____2661 in
                     if uu____2660
                     then
                       let uu____2663 = FStar_Syntax_Print.term_to_string l1 in
                       let uu____2664 = FStar_Syntax_Print.term_to_string r1 in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____2663 uu____2664
                     else (solve g FStar_Syntax_Const.exp_unit; dismiss)
                 | (hd2,uu____2668) ->
                     let uu____2679 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____2679))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___102_2689 = ps in
              {
                main_context = (uu___102_2689.main_context);
                main_goal = (uu___102_2689.main_goal);
                all_implicits = (uu___102_2689.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___102_2689.smt_goals)
              })
       | uu____2690 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___103_2698 = ps in
              {
                main_context = (uu___103_2698.main_context);
                main_goal = (uu___103_2698.main_goal);
                all_implicits = (uu___103_2698.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___103_2698.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2702 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2716 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2716 with
         | (t1,typ,guard) ->
             let uu____2726 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2726 with
              | (hd1,args) ->
                  let uu____2755 =
                    let uu____2763 =
                      let uu____2764 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2764.FStar_Syntax_Syntax.n in
                    (uu____2763, args) in
                  (match uu____2755 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2777)::(q,uu____2779)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___104_2808 = g in
                         let uu____2809 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2809;
                           witness = (uu___104_2808.witness);
                           goal_ty = (uu___104_2808.goal_ty);
                           opts = (uu___104_2808.opts)
                         } in
                       let g2 =
                         let uu___105_2811 = g in
                         let uu____2812 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2812;
                           witness = (uu___105_2811.witness);
                           goal_ty = (uu___105_2811.goal_ty);
                           opts = (uu___105_2811.opts)
                         } in
                       bind dismiss
                         (fun uu____2815  ->
                            let uu____2816 = add_goals [g1; g2] in
                            bind uu____2816
                              (fun uu____2820  ->
                                 let uu____2821 =
                                   let uu____2824 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____2825 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____2824, uu____2825) in
                                 ret uu____2821))
                   | uu____2828 ->
                       let uu____2836 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____2836)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____2847 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____2847);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___106_2853 = g in
                 {
                   context = (uu___106_2853.context);
                   witness = (uu___106_2853.witness);
                   goal_ty = (uu___106_2853.goal_ty);
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
      let uu____2876 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____2876 with
      | (u,uu____2886,g_u) ->
          let g =
            let uu____2895 = FStar_Options.peek () in
            { context = env; witness = u; goal_ty = typ; opts = uu____2895 } in
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            } in
          (ps, u)