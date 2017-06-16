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
let add_irrelevant_goal: env -> FStar_Syntax_Syntax.typ -> Prims.unit tac =
  fun env  ->
    fun phi  ->
      bind cur_goal
        (fun cur  ->
           let typ = FStar_Syntax_Util.mk_squash phi in
           let uu____787 = new_uvar env typ in
           bind uu____787
             (fun uu____793  ->
                match uu____793 with
                | (u,g_u) ->
                    let goal =
                      {
                        context = env;
                        witness = u;
                        goal_ty = typ;
                        opts = (cur.opts)
                      } in
                    add_goals [goal]))
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____802 = is_irrelevant g in
       if uu____802
       then bind dismiss (fun uu____804  -> add_smt_goals [g])
       else
         (let uu____806 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____806))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____836 =
         try let uu____853 = FStar_List.splitAt n1 p.goals in ret uu____853
         with | uu____868 -> fail "divide: not enough goals" in
       bind uu____836
         (fun uu____879  ->
            match uu____879 with
            | (lgs,rgs) ->
                let lp =
                  let uu___84_894 = p in
                  {
                    main_context = (uu___84_894.main_context);
                    main_goal = (uu___84_894.main_goal);
                    all_implicits = (uu___84_894.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___85_896 = p in
                  {
                    main_context = (uu___85_896.main_context);
                    main_goal = (uu___85_896.main_goal);
                    all_implicits = (uu___85_896.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____897 = set lp in
                bind uu____897
                  (fun uu____901  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____908 = set rp in
                               bind uu____908
                                 (fun uu____912  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___86_920 = p in
                                                {
                                                  main_context =
                                                    (uu___86_920.main_context);
                                                  main_goal =
                                                    (uu___86_920.main_goal);
                                                  all_implicits =
                                                    (uu___86_920.all_implicits);
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
                                              let uu____921 = set p' in
                                              bind uu____921
                                                (fun uu____925  -> ret (a, b))))))))))
let focus f =
  let uu____938 = divide (Prims.parse_int "1") f idtac in
  bind uu____938 (fun uu____944  -> match uu____944 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____965::uu____966 ->
           let uu____968 =
             let uu____973 = map tau in
             divide (Prims.parse_int "1") tau uu____973 in
           bind uu____968
             (fun uu____981  -> match uu____981 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1004 =
        bind t1
          (fun uu____1006  ->
             let uu____1007 = map t2 in
             bind uu____1007 (fun uu____1011  -> ret ())) in
      focus uu____1004
let intro: (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____1019 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1019 with
       | Some (b,c) ->
           let uu____1030 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1030 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1050 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1053 =
                  let uu____1054 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1054 in
                if uu____1053
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1067 = new_uvar env' typ' in
                   bind uu____1067
                     (fun uu____1075  ->
                        match uu____1075 with
                        | (u,g) ->
                            let uu____1083 =
                              let uu____1084 =
                                FStar_Syntax_Util.abs [b1] u None in
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                goal.witness uu____1084 in
                            if uu____1083
                            then
                              let uu____1097 =
                                let uu____1099 =
                                  let uu___89_1100 = goal in
                                  let uu____1101 = bnorm env' u in
                                  let uu____1102 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1101;
                                    goal_ty = uu____1102;
                                    opts = (uu___89_1100.opts)
                                  } in
                                replace_cur uu____1099 in
                              bind uu____1097 (fun uu____1105  -> ret b1)
                            else fail "intro: unification failed")))
       | None  ->
           let uu____1113 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1113)
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
           let uu____1132 =
             let uu____1134 = FStar_List.map tr s in
             FStar_List.flatten uu____1134 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1132 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___90_1140 = goal in
            {
              context = (uu___90_1140.context);
              witness = w;
              goal_ty = t;
              opts = (uu___90_1140.opts)
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
       let uu____1152 = istrivial goal.context goal.goal_ty in
       if uu____1152
       then (solve goal FStar_Syntax_Const.exp_unit; dismiss)
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
                                    add_irrelevant_goal goal.context pre))
                            else
                              (let uu____1357 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1358 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1359 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1357 uu____1358 uu____1359)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1368 =
          let uu____1372 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1372 in
        FStar_List.map FStar_Pervasives.fst uu____1368 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1395 = let uu____1398 = exact tm in trytac uu____1398 in
           bind uu____1395
             (fun r  ->
                match r with
                | Some r1 -> ret ()
                | None  ->
                    let uu____1405 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1405 with
                     | (tm1,typ,guard) ->
                         let uu____1413 =
                           let uu____1414 =
                             let uu____1415 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1415 in
                           Prims.op_Negation uu____1414 in
                         if uu____1413
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1418 = FStar_Syntax_Util.arrow_one typ in
                            match uu____1418 with
                            | None  ->
                                let uu____1425 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1425
                            | Some ((bv,aq),c) ->
                                let uu____1435 =
                                  let uu____1436 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____1436 in
                                if uu____1435
                                then fail "apply: not total"
                                else
                                  (let uu____1439 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____1439
                                     (fun uu____1445  ->
                                        match uu____1445 with
                                        | (u,g_u) ->
                                            let tm' =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                tm1 [(u, aq)] None
                                                (goal.context).FStar_TypeChecker_Env.range in
                                            let uu____1460 = __apply uopt tm' in
                                            bind uu____1460
                                              (fun uu____1462  ->
                                                 let uu____1463 =
                                                   let uu____1464 =
                                                     let uu____1467 =
                                                       let uu____1468 =
                                                         FStar_Syntax_Util.head_and_args
                                                           u in
                                                       fst uu____1468 in
                                                     FStar_Syntax_Subst.compress
                                                       uu____1467 in
                                                   uu____1464.FStar_Syntax_Syntax.n in
                                                 match uu____1463 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     (uvar,uu____1487) ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1501 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____1501
                                                          then ret ()
                                                          else
                                                            (let uu____1504 =
                                                               let uu____1506
                                                                 =
                                                                 let uu____1507
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____1508
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1507;
                                                                   goal_ty =
                                                                    uu____1508;
                                                                   opts =
                                                                    (goal.opts)
                                                                 } in
                                                               [uu____1506] in
                                                             add_goals
                                                               uu____1504))
                                                 | uu____1509 -> ret ())))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1515 = __apply true tm in focus uu____1515
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1523 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1523 with
         | (tm1,t,guard) ->
             let uu____1531 =
               let uu____1532 =
                 let uu____1533 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1533 in
               Prims.op_Negation uu____1532 in
             if uu____1531
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1536 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____1536 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____1553 =
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
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____1643,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____1553 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1675 =
                             let uu____1682 =
                               let uu____1688 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____1688.FStar_Syntax_Syntax.effect_args in
                             match uu____1682 with
                             | pre::post::uu____1697 ->
                                 ((fst pre), (fst post))
                             | uu____1727 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
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
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1791  ->
                                               match uu____1791 with
                                               | (uu____1798,uu____1799,uu____1800,tm2,uu____1802,uu____1803)
                                                   ->
                                                   let uu____1804 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1804 with
                                                    | (hd1,uu____1815) ->
                                                        let uu____1830 =
                                                          let uu____1831 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1831.FStar_Syntax_Syntax.n in
                                                        (match uu____1830
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1834 ->
                                                             true
                                                         | uu____1843 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____1845  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____1855 =
                                                 let uu____1859 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____1859 in
                                               FStar_List.map
                                                 FStar_Pervasives.fst
                                                 uu____1855 in
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
                                             let uu____1887 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
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
                                                           bnorm goal.context
                                                             term in
                                                         let uu____1958 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____1957;
                                                           goal_ty =
                                                             uu____1958;
                                                           opts = (goal.opts)
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____1990 = f x xs1 in
                                                 if uu____1990
                                                 then
                                                   let uu____1992 =
                                                     filter' f xs1 in
                                                   x :: uu____1992
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____2000 =
                                                      checkone g1.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____2000) sub_goals in
                                           let uu____2001 =
                                             add_irrelevant_goal goal.context
                                               pre in
                                           bind uu____2001
                                             (fun uu____2003  ->
                                                let uu____2004 =
                                                  trytac trivial in
                                                bind uu____2004
                                                  (fun uu____2008  ->
                                                     let uu____2010 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits in
                                                     bind uu____2010
                                                       (fun uu____2012  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2019 =
           FStar_All.pipe_left mlog
             (fun uu____2024  ->
                let uu____2025 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2026 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2025
                  uu____2026) in
         bind uu____2019
           (fun uu____2027  ->
              let uu____2028 =
                let uu____2030 =
                  let uu____2031 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2031 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2030 in
              match uu____2028 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2038::(x,uu____2040)::(e,uu____2042)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2076 =
                    let uu____2077 = FStar_Syntax_Subst.compress x in
                    uu____2077.FStar_Syntax_Syntax.n in
                  (match uu____2076 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___95_2083 = goal in
                         let uu____2084 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2087 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___95_2083.context);
                           witness = uu____2084;
                           goal_ty = uu____2087;
                           opts = (uu___95_2083.opts)
                         } in
                       replace_cur goal1
                   | uu____2090 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2091 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2095 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2095 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2110 = FStar_Util.set_mem x fns_ty in
           if uu____2110
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2113 = new_uvar env' goal.goal_ty in
              bind uu____2113
                (fun uu____2119  ->
                   match uu____2119 with
                   | (u,g) ->
                       let uu____2125 =
                         let uu____2126 =
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness u in
                         Prims.op_Negation uu____2126 in
                       if uu____2125
                       then fail "clear: unification failed"
                       else
                         (let new_goal =
                            let uu___96_2130 = goal in
                            let uu____2131 = bnorm env' u in
                            {
                              context = env';
                              witness = uu____2131;
                              goal_ty = (uu___96_2130.goal_ty);
                              opts = (uu___96_2130.opts)
                            } in
                          bind dismiss
                            (fun uu____2132  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2139 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2139 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2154 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2154 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2168 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2168 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___97_2191 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___97_2191.opts)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2198 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2198 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2210 = FStar_Syntax_Print.bv_to_string x in
               let uu____2211 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2210 uu____2211
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2224 = revert_all_hd xs1 in
        bind uu____2224 (fun uu____2226  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___98_2236 = g in
           {
             context = ctx';
             witness = (uu___98_2236.witness);
             goal_ty = (uu___98_2236.goal_ty);
             opts = (uu___98_2236.opts)
           } in
         bind dismiss (fun uu____2237  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___99_2247 = g in
           {
             context = ctx';
             witness = (uu___99_2247.witness);
             goal_ty = (uu___99_2247.goal_ty);
             opts = (uu___99_2247.opts)
           } in
         bind dismiss (fun uu____2248  -> add_goals [g']))
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2278 = f x in
      bind uu____2278
        (fun y  ->
           let uu____2282 = mapM f xs in
           bind uu____2282 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2314 = FStar_Syntax_Subst.compress t in
          uu____2314.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2340 = ff hd1 in
              bind uu____2340
                (fun hd2  ->
                   let fa uu____2351 =
                     match uu____2351 with
                     | (a,q) ->
                         let uu____2359 = ff a in
                         bind uu____2359 (fun a1  -> ret (a1, q)) in
                   let uu____2366 = mapM fa args in
                   bind uu____2366
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2410 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2410 with
               | (bs1,t') ->
                   let uu____2416 =
                     let uu____2418 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2418 t' in
                   bind uu____2416
                     (fun t''  ->
                        let uu____2420 =
                          let uu____2421 =
                            let uu____2436 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____2437 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____2436, uu____2437, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2421 in
                        ret uu____2420))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2456 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___100_2458 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___100_2458.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___100_2458.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___100_2458.FStar_Syntax_Syntax.vars)
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
          let uu____2479 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2479 with
          | (t1,lcomp,g) ->
              let uu____2487 =
                (let uu____2488 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2488) ||
                  (let uu____2489 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2489) in
              if uu____2487
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2495 = new_uvar env typ in
                 bind uu____2495
                   (fun uu____2501  ->
                      match uu____2501 with
                      | (ut,guard) ->
                          (log ps
                             (fun uu____2508  ->
                                let uu____2509 =
                                  FStar_Syntax_Print.term_to_string t1 in
                                let uu____2510 =
                                  FStar_Syntax_Print.term_to_string ut in
                                FStar_Util.print2
                                  "Pointwise_rec: making equality %s = %s\n"
                                  uu____2509 uu____2510);
                           (let uu____2511 =
                              let uu____2513 =
                                let uu____2514 =
                                  FStar_TypeChecker_TcTerm.universe_of env
                                    typ in
                                FStar_Syntax_Util.mk_eq2 uu____2514 typ t1 ut in
                              add_irrelevant_goal env uu____2513 in
                            bind uu____2511
                              (fun uu____2515  ->
                                 let uu____2516 =
                                   bind tau
                                     (fun uu____2518  ->
                                        FStar_TypeChecker_Rel.force_trivial_guard
                                          env guard;
                                        (let ut1 =
                                           FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                             env ut in
                                         ret ut1)) in
                                 focus uu____2516)))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2529 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2529 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2550  ->
                   let uu____2551 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2551);
              bind dismiss_all
                (fun uu____2552  ->
                   let uu____2553 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2553
                     (fun gt'  ->
                        log ps
                          (fun uu____2557  ->
                             let uu____2558 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2558);
                        (let uu____2559 = push_goals gs in
                         bind uu____2559
                           (fun uu____2561  ->
                              add_goals
                                [(let uu___101_2562 = g in
                                  {
                                    context = (uu___101_2562.context);
                                    witness = (uu___101_2562.witness);
                                    goal_ty = gt';
                                    opts = (uu___101_2562.opts)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2565 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2565 with
       | Some t ->
           let uu____2575 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2575 with
            | (hd1,args) ->
                let uu____2596 =
                  let uu____2604 =
                    let uu____2605 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2605.FStar_Syntax_Syntax.n in
                  (uu____2604, args) in
                (match uu____2596 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2615::(l,uu____2617)::(r,uu____2619)::[]) when
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
                     let uu____2655 =
                       let uu____2656 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l1 r1 in
                       Prims.op_Negation uu____2656 in
                     if uu____2655
                     then
                       let uu____2658 = FStar_Syntax_Print.term_to_string l1 in
                       let uu____2659 = FStar_Syntax_Print.term_to_string r1 in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____2658 uu____2659
                     else (solve g FStar_Syntax_Const.exp_unit; dismiss)
                 | (hd2,uu____2663) ->
                     let uu____2674 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____2674))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___102_2684 = ps in
              {
                main_context = (uu___102_2684.main_context);
                main_goal = (uu___102_2684.main_goal);
                all_implicits = (uu___102_2684.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___102_2684.smt_goals)
              })
       | uu____2685 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___103_2693 = ps in
              {
                main_context = (uu___103_2693.main_context);
                main_goal = (uu___103_2693.main_goal);
                all_implicits = (uu___103_2693.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___103_2693.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2697 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2711 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2711 with
         | (t1,typ,guard) ->
             let uu____2721 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2721 with
              | (hd1,args) ->
                  let uu____2750 =
                    let uu____2758 =
                      let uu____2759 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2759.FStar_Syntax_Syntax.n in
                    (uu____2758, args) in
                  (match uu____2750 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2772)::(q,uu____2774)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___104_2803 = g in
                         let uu____2804 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2804;
                           witness = (uu___104_2803.witness);
                           goal_ty = (uu___104_2803.goal_ty);
                           opts = (uu___104_2803.opts)
                         } in
                       let g2 =
                         let uu___105_2806 = g in
                         let uu____2807 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2807;
                           witness = (uu___105_2806.witness);
                           goal_ty = (uu___105_2806.goal_ty);
                           opts = (uu___105_2806.opts)
                         } in
                       bind dismiss
                         (fun uu____2810  ->
                            let uu____2811 = add_goals [g1; g2] in
                            bind uu____2811
                              (fun uu____2815  ->
                                 let uu____2816 =
                                   let uu____2819 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____2820 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____2819, uu____2820) in
                                 ret uu____2816))
                   | uu____2823 ->
                       let uu____2831 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____2831)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____2842 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____2842);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___106_2848 = g in
                 {
                   context = (uu___106_2848.context);
                   witness = (uu___106_2848.witness);
                   goal_ty = (uu___106_2848.goal_ty);
                   opts = opts'
                 } in
               replace_cur g'
           | FStar_Getopt.Error err1 ->
               fail2 "Setting options `%s` failed: %s" s err1
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
let cur_env: env tac =
  bind get
    (fun ps  ->
       let uu____2852 =
         let uu____2853 = FStar_List.hd ps.goals in uu____2853.context in
       FStar_All.pipe_left ret uu____2852)
let cur_goal': FStar_Syntax_Syntax.typ tac =
  bind get
    (fun ps  ->
       let uu____2857 =
         let uu____2858 = FStar_List.hd ps.goals in uu____2858.goal_ty in
       FStar_All.pipe_left ret uu____2857)
let cur_witness: FStar_Syntax_Syntax.term tac =
  bind get
    (fun ps  ->
       let uu____2862 =
         let uu____2863 = FStar_List.hd ps.goals in uu____2863.witness in
       FStar_All.pipe_left ret uu____2862)
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> (proofstate* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      let uu____2877 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____2877 with
      | (u,uu____2887,g_u) ->
          let g =
            let uu____2896 = FStar_Options.peek () in
            { context = env; witness = u; goal_ty = typ; opts = uu____2896 } in
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            } in
          (ps, u)