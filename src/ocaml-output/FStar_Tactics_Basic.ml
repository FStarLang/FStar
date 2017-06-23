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
  | Success of ('a,proofstate) FStar_Pervasives_Native.tuple2
  | Failed of (Prims.string,proofstate) FStar_Pervasives_Native.tuple2
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
       let uu____354 = run t1 p in
       match uu____354 with
       | Success (a,q) -> let uu____359 = t2 a in run uu____359 q
       | Failed (msg,q) -> Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____369 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____369
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____370 = FStar_Syntax_Print.term_to_string g.witness in
    let uu____371 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____370 uu____371
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____384 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____384
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____397 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____397
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____414 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____414
let comp_to_typ:
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____420) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____428) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: goal -> Prims.bool =
  fun g  ->
    let uu____440 =
      let uu____444 =
        FStar_TypeChecker_Normalize.unfold_whnf g.context g.goal_ty in
      FStar_Syntax_Util.un_squash uu____444 in
    match uu____440 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____450 -> false
let dump_goal ps goal =
  let uu____470 = goal_to_string goal in tacprint uu____470
let dump_cur: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____480 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____483 = FStar_List.hd ps.goals in dump_goal ps uu____483))
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____495 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____495);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____504 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____504);
      FStar_List.iter (dump_goal ps) ps.smt_goals
let print_proof_state1: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_cur p msg; Success ((), p))
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let tac_verb_dbg: Prims.bool FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let rec log: proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun ps  ->
    fun f  ->
      let uu____553 = FStar_ST.read tac_verb_dbg in
      match uu____553 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____559 =
              let uu____561 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____561 in
            FStar_ST.write tac_verb_dbg uu____559);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____594 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____594
        then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
        else ());
       Failed (msg, ps))
let fail1 msg x = let uu____612 = FStar_Util.format1 msg x in fail uu____612
let fail2 msg x y =
  let uu____635 = FStar_Util.format2 msg x y in fail uu____635
let fail3 msg x y z =
  let uu____664 = FStar_Util.format3 msg x y z in fail uu____664
let trytac t =
  mk_tac
    (fun ps  ->
       let tx = FStar_Syntax_Unionfind.new_transaction () in
       let uu____687 = run t ps in
       match uu____687 with
       | Success (a,q) ->
           (FStar_Syntax_Unionfind.commit tx;
            Success ((FStar_Pervasives_Native.Some a), q))
       | Failed (uu____696,uu____697) ->
           (FStar_Syntax_Unionfind.rollback tx;
            Success (FStar_Pervasives_Native.None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____708  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____717 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____717
      then ()
      else
        (let uu____719 =
           let uu____720 =
             let uu____721 = FStar_Syntax_Print.term_to_string solution in
             let uu____722 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____723 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____721
               uu____722 uu____723 in
           TacFailure uu____720 in
         raise uu____719)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____728 =
         let uu___78_729 = p in
         let uu____730 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_729.main_context);
           main_goal = (uu___78_729.main_goal);
           all_implicits = (uu___78_729.all_implicits);
           goals = uu____730;
           smt_goals = (uu___78_729.smt_goals)
         } in
       set uu____728)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_737 = p in
          {
            main_context = (uu___79_737.main_context);
            main_goal = (uu___79_737.main_goal);
            all_implicits = (uu___79_737.all_implicits);
            goals = [];
            smt_goals = (uu___79_737.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_750 = p in
            {
              main_context = (uu___80_750.main_context);
              main_goal = (uu___80_750.main_goal);
              all_implicits = (uu___80_750.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_750.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_763 = p in
            {
              main_context = (uu___81_763.main_context);
              main_goal = (uu___81_763.main_goal);
              all_implicits = (uu___81_763.all_implicits);
              goals = (uu___81_763.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_776 = p in
            {
              main_context = (uu___82_776.main_context);
              main_goal = (uu___82_776.main_goal);
              all_implicits = (uu___82_776.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___82_776.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_789 = p in
            {
              main_context = (uu___83_789.main_context);
              main_goal = (uu___83_789.main_goal);
              all_implicits = (uu___83_789.all_implicits);
              goals = (uu___83_789.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____797  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_808 = p in
            {
              main_context = (uu___84_808.main_context);
              main_goal = (uu___84_808.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_808.goals);
              smt_goals = (uu___84_808.smt_goals)
            }))
let new_uvar:
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2 tac
  =
  fun env  ->
    fun typ  ->
      let uu____829 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____829 with
      | (u,uu____840,g_u) ->
          let uu____848 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____848 (fun uu____853  -> ret (u, g_u))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____860 = FStar_Syntax_Util.un_squash t in
    match uu____860 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____869 =
          let uu____870 = FStar_Syntax_Subst.compress t' in
          uu____870.FStar_Syntax_Syntax.n in
        (match uu____869 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____874 -> false)
    | uu____875 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____883 = FStar_Syntax_Util.un_squash t in
    match uu____883 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____892 =
          let uu____893 = FStar_Syntax_Subst.compress t' in
          uu____893.FStar_Syntax_Syntax.n in
        (match uu____892 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____897 -> false)
    | uu____898 -> false
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
        let uu____926 = new_uvar env typ in
        bind uu____926
          (fun uu____936  ->
             match uu____936 with
             | (u,g_u) ->
                 let goal =
                   { context = env; witness = u; goal_ty = typ; opts } in
                 add_goals [goal])
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____947 = is_irrelevant g in
       if uu____947
       then bind dismiss (fun uu____950  -> add_smt_goals [g])
       else
         (let uu____952 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____952))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____989 =
         try let uu____1008 = FStar_List.splitAt n1 p.goals in ret uu____1008
         with | uu____1025 -> fail "divide: not enough goals" in
       bind uu____989
         (fun uu____1042  ->
            match uu____1042 with
            | (lgs,rgs) ->
                let lp =
                  let uu___85_1057 = p in
                  {
                    main_context = (uu___85_1057.main_context);
                    main_goal = (uu___85_1057.main_goal);
                    all_implicits = (uu___85_1057.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___86_1059 = p in
                  {
                    main_context = (uu___86_1059.main_context);
                    main_goal = (uu___86_1059.main_goal);
                    all_implicits = (uu___86_1059.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____1060 = set lp in
                bind uu____1060
                  (fun uu____1065  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____1075 = set rp in
                               bind uu____1075
                                 (fun uu____1080  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___87_1092 = p in
                                                {
                                                  main_context =
                                                    (uu___87_1092.main_context);
                                                  main_goal =
                                                    (uu___87_1092.main_goal);
                                                  all_implicits =
                                                    (uu___87_1092.all_implicits);
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
                                              let uu____1093 = set p' in
                                              bind uu____1093
                                                (fun uu____1098  ->
                                                   ret (a, b))))))))))
let focus f =
  let uu____1113 = divide (Prims.parse_int "1") f idtac in
  bind uu____1113
    (fun uu____1121  -> match uu____1121 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____1145::uu____1146 ->
           let uu____1148 =
             let uu____1153 = map tau in
             divide (Prims.parse_int "1") tau uu____1153 in
           bind uu____1148
             (fun uu____1164  ->
                match uu____1164 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1189 =
        bind t1
          (fun uu____1193  ->
             let uu____1194 = map t2 in
             bind uu____1194 (fun uu____1199  -> ret ())) in
      focus uu____1189
let intro:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 tac
  =
  bind cur_goal
    (fun goal  ->
       let uu____1216 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1216 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1227 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1227 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1247 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1250 =
                  let uu____1251 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1251 in
                if uu____1250
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1264 = new_uvar env' typ' in
                   bind uu____1264
                     (fun uu____1277  ->
                        match uu____1277 with
                        | (u,g) ->
                            let uu____1285 =
                              let uu____1286 =
                                FStar_Syntax_Util.abs [b1] u
                                  FStar_Pervasives_Native.None in
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                goal.witness uu____1286 in
                            if uu____1285
                            then
                              let uu____1294 =
                                let uu____1296 =
                                  let uu___90_1297 = goal in
                                  let uu____1298 = bnorm env' u in
                                  let uu____1299 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1298;
                                    goal_ty = uu____1299;
                                    opts = (uu___90_1297.opts)
                                  } in
                                replace_cur uu____1296 in
                              bind uu____1294 (fun uu____1303  -> ret b1)
                            else fail "intro: unification failed")))
       | FStar_Pervasives_Native.None  ->
           let uu____1311 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1311)
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
           let uu____1336 =
             let uu____1338 = FStar_List.map tr s in
             FStar_List.flatten uu____1338 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1336 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___91_1346 = goal in
            {
              context = (uu___91_1346.context);
              witness = w;
              goal_ty = t;
              opts = (uu___91_1346.opts)
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
       let uu____1363 = istrivial goal.context goal.goal_ty in
       if uu____1363
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____1367 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1367))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1377 =
           try
             let uu____1393 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1393
           with
           | e ->
               let uu____1410 = FStar_Syntax_Print.term_to_string t in
               let uu____1411 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1410
                 uu____1411 in
         bind uu____1377
           (fun uu____1423  ->
              match uu____1423 with
              | (t1,typ,guard) ->
                  let uu____1431 =
                    let uu____1432 =
                      let uu____1433 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1433 in
                    Prims.op_Negation uu____1432 in
                  if uu____1431
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1436 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1436
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1440 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1441 =
                          let uu____1442 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1442 in
                        let uu____1443 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1440 uu____1441 uu____1443))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1453 =
           try
             let uu____1469 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1469
           with
           | e ->
               let uu____1486 = FStar_Syntax_Print.term_to_string t in
               let uu____1487 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1486
                 uu____1487 in
         bind uu____1453
           (fun uu____1499  ->
              match uu____1499 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1512 =
                       let uu____1513 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1513 in
                     if uu____1512
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1516 =
                          let uu____1523 =
                            let uu____1529 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1529.FStar_Syntax_Syntax.effect_args in
                          match uu____1523 with
                          | pre::post::uu____1538 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____1568 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1516 with
                        | (pre,post) ->
                            let uu____1591 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1591
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1595  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____1597 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1598 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1599 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1597 uu____1598 uu____1599)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1610 =
          let uu____1614 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1614 in
        FStar_List.map FStar_Pervasives_Native.fst uu____1610 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1643 = let uu____1646 = exact tm in trytac uu____1646 in
           bind uu____1643
             (fun r  ->
                match r with
                | FStar_Pervasives_Native.Some r1 -> ret ()
                | FStar_Pervasives_Native.None  ->
                    let uu____1655 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1655 with
                     | (tm1,typ,guard) ->
                         let uu____1663 =
                           let uu____1664 =
                             let uu____1665 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1665 in
                           Prims.op_Negation uu____1664 in
                         if uu____1663
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1668 = FStar_Syntax_Util.arrow_one typ in
                            match uu____1668 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____1675 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1675
                            | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                let uu____1685 =
                                  let uu____1686 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____1686 in
                                if uu____1685
                                then fail "apply: not total"
                                else
                                  (let uu____1689 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____1689
                                     (fun uu____1700  ->
                                        match uu____1700 with
                                        | (u,g_u) ->
                                            let tm' =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                tm1 [(u, aq)]
                                                FStar_Pervasives_Native.None
                                                (goal.context).FStar_TypeChecker_Env.range in
                                            let uu____1715 = __apply uopt tm' in
                                            bind uu____1715
                                              (fun uu____1721  ->
                                                 let uu____1722 =
                                                   let uu____1723 =
                                                     let uu____1726 =
                                                       let uu____1727 =
                                                         FStar_Syntax_Util.head_and_args
                                                           u in
                                                       FStar_Pervasives_Native.fst
                                                         uu____1727 in
                                                     FStar_Syntax_Subst.compress
                                                       uu____1726 in
                                                   uu____1723.FStar_Syntax_Syntax.n in
                                                 match uu____1722 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     (uvar,uu____1746) ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1766 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____1766
                                                          then ret ()
                                                          else
                                                            (let uu____1769 =
                                                               let uu____1771
                                                                 =
                                                                 let uu____1772
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____1773
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1772;
                                                                   goal_ty =
                                                                    uu____1773;
                                                                   opts =
                                                                    (goal.opts)
                                                                 } in
                                                               [uu____1771] in
                                                             add_goals
                                                               uu____1769))
                                                 | uu____1774 -> ret ())))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1781 = __apply true tm in focus uu____1781
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1796 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1796 with
         | (tm1,t,guard) ->
             let uu____1804 =
               let uu____1805 =
                 let uu____1806 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1806 in
               Prims.op_Negation uu____1805 in
             if uu____1804
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1809 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____1809 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____1826 =
                         FStar_List.fold_left
                           (fun uu____1856  ->
                              fun uu____1857  ->
                                match (uu____1856, uu____1857) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____1906 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____1906 with
                                     | (u,uu____1921,g_u) ->
                                         let uu____1929 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____1929,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____1826 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1961 =
                             let uu____1968 =
                               let uu____1974 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____1974.FStar_Syntax_Syntax.effect_args in
                             match uu____1968 with
                             | pre::post::uu____1983 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____2013 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____1961 with
                            | (pre,post) ->
                                let uu____2036 =
                                  let uu____2038 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____2038 goal.goal_ty in
                                (match uu____2036 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____2040 =
                                       let uu____2041 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____2041 in
                                     let uu____2042 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____2040 uu____2042
                                 | FStar_Pervasives_Native.Some g ->
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____2089  ->
                                               match uu____2089 with
                                               | (uu____2096,uu____2097,uu____2098,tm2,uu____2100,uu____2101)
                                                   ->
                                                   let uu____2102 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____2102 with
                                                    | (hd1,uu____2113) ->
                                                        let uu____2128 =
                                                          let uu____2129 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____2129.FStar_Syntax_Syntax.n in
                                                        (match uu____2128
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____2132 ->
                                                             true
                                                         | uu____2143 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____2153  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____2163 =
                                                 let uu____2167 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____2167 in
                                               FStar_List.map
                                                 FStar_Pervasives_Native.fst
                                                 uu____2163 in
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
                                             let uu____2197 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____2197 with
                                             | (hd1,uu____2208) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____2224) ->
                                                      appears uv goals
                                                  | uu____2241 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____2267  ->
                                                     match uu____2267 with
                                                     | (_msg,_env,_uvar,term,typ,uu____2279)
                                                         ->
                                                         let uu____2280 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____2281 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____2280;
                                                           goal_ty =
                                                             uu____2281;
                                                           opts = (goal.opts)
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____2313 = f x xs1 in
                                                 if uu____2313
                                                 then
                                                   let uu____2315 =
                                                     filter' f xs1 in
                                                   x :: uu____2315
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____2326 =
                                                      checkone g1.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____2326) sub_goals in
                                           let uu____2327 =
                                             add_irrelevant_goal goal.context
                                               pre goal.opts in
                                           bind uu____2327
                                             (fun uu____2331  ->
                                                let uu____2332 =
                                                  trytac trivial in
                                                bind uu____2332
                                                  (fun uu____2338  ->
                                                     let uu____2340 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits in
                                                     bind uu____2340
                                                       (fun uu____2343  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2353 =
           FStar_All.pipe_left mlog
             (fun uu____2361  ->
                let uu____2362 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____2363 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2362
                  uu____2363) in
         bind uu____2353
           (fun uu____2375  ->
              let uu____2376 =
                let uu____2378 =
                  let uu____2379 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____2379 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2378 in
              match uu____2376 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2386::(x,uu____2388)::(e,uu____2390)::[])) when
                  FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
                  let uu____2424 =
                    let uu____2425 = FStar_Syntax_Subst.compress x in
                    uu____2425.FStar_Syntax_Syntax.n in
                  (match uu____2424 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___96_2431 = goal in
                         let uu____2432 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2435 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___96_2431.context);
                           witness = uu____2432;
                           goal_ty = uu____2435;
                           opts = (uu___96_2431.opts)
                         } in
                       replace_cur goal1
                   | uu____2438 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2439 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2445 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2445 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2460 = FStar_Util.set_mem x fns_ty in
           if uu____2460
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2463 = new_uvar env' goal.goal_ty in
              bind uu____2463
                (fun uu____2473  ->
                   match uu____2473 with
                   | (u,g) ->
                       let uu____2479 =
                         let uu____2480 =
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness u in
                         Prims.op_Negation uu____2480 in
                       if uu____2479
                       then fail "clear: unification failed"
                       else
                         (let new_goal =
                            let uu___97_2484 = goal in
                            let uu____2485 = bnorm env' u in
                            {
                              context = env';
                              witness = uu____2485;
                              goal_ty = (uu___97_2484.goal_ty);
                              opts = (uu___97_2484.opts)
                            } in
                          bind dismiss
                            (fun uu____2487  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2497 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2497 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2514 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2514 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____2528 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____2528 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___98_2548 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___98_2548.opts)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2558 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2558 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2570 = FStar_Syntax_Print.bv_to_string x in
               let uu____2571 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2570 uu____2571
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2584 = revert_all_hd xs1 in
        bind uu____2584 (fun uu____2587  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___99_2602 = g in
           {
             context = ctx';
             witness = (uu___99_2602.witness);
             goal_ty = (uu___99_2602.goal_ty);
             opts = (uu___99_2602.opts)
           } in
         bind dismiss (fun uu____2604  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___100_2619 = g in
           {
             context = ctx';
             witness = (uu___100_2619.witness);
             goal_ty = (uu___100_2619.goal_ty);
             opts = (uu___100_2619.opts)
           } in
         bind dismiss (fun uu____2621  -> add_goals [g']))
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2655 = f x in
      bind uu____2655
        (fun y  ->
           let uu____2661 = mapM f xs in
           bind uu____2661 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2697 = FStar_Syntax_Subst.compress t in
          uu____2697.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2723 = ff hd1 in
              bind uu____2723
                (fun hd2  ->
                   let fa uu____2737 =
                     match uu____2737 with
                     | (a,q) ->
                         let uu____2745 = ff a in
                         bind uu____2745 (fun a1  -> ret (a1, q)) in
                   let uu____2753 = mapM fa args in
                   bind uu____2753
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2788 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2788 with
               | (bs1,t') ->
                   let uu____2794 =
                     let uu____2796 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2796 t' in
                   bind uu____2794
                     (fun t''  ->
                        let uu____2800 =
                          let uu____2801 =
                            let uu____2811 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____2812 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____2811, uu____2812, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2801 in
                        ret uu____2800))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2826 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___101_2830 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___101_2830.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___101_2830.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___101_2830.FStar_Syntax_Syntax.vars)
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
            let uu____2859 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____2859 with
            | (t1,lcomp,g) ->
                let uu____2867 =
                  (let uu____2870 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____2870) ||
                    (let uu____2872 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____2872) in
                if uu____2867
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____2878 = new_uvar env typ in
                   bind uu____2878
                     (fun uu____2889  ->
                        match uu____2889 with
                        | (ut,guard) ->
                            (log ps
                               (fun uu____2899  ->
                                  let uu____2900 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  let uu____2901 =
                                    FStar_Syntax_Print.term_to_string ut in
                                  FStar_Util.print2
                                    "Pointwise_rec: making equality %s = %s\n"
                                    uu____2900 uu____2901);
                             (let uu____2902 =
                                let uu____2904 =
                                  let uu____2905 =
                                    FStar_TypeChecker_TcTerm.universe_of env
                                      typ in
                                  FStar_Syntax_Util.mk_eq2 uu____2905 typ t1
                                    ut in
                                add_irrelevant_goal env uu____2904 opts in
                              bind uu____2902
                                (fun uu____2908  ->
                                   let uu____2909 =
                                     bind tau
                                       (fun uu____2914  ->
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env guard;
                                          (let ut1 =
                                             FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                               env ut in
                                           ret ut1)) in
                                   focus uu____2909)))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2932 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2932 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2955  ->
                   let uu____2956 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2956);
              bind dismiss_all
                (fun uu____2959  ->
                   let uu____2960 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____2960
                     (fun gt'  ->
                        log ps
                          (fun uu____2969  ->
                             let uu____2970 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2970);
                        (let uu____2971 = push_goals gs in
                         bind uu____2971
                           (fun uu____2974  ->
                              add_goals
                                [(let uu___102_2976 = g in
                                  {
                                    context = (uu___102_2976.context);
                                    witness = (uu___102_2976.witness);
                                    goal_ty = gt';
                                    opts = (uu___102_2976.opts)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2997 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2997 with
       | FStar_Pervasives_Native.Some t ->
           let uu____3007 = FStar_Syntax_Util.head_and_args' t in
           (match uu____3007 with
            | (hd1,args) ->
                let uu____3028 =
                  let uu____3036 =
                    let uu____3037 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____3037.FStar_Syntax_Syntax.n in
                  (uu____3036, args) in
                (match uu____3028 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3047::(l,uu____3049)::(r,uu____3051)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
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
                     let uu____3087 =
                       let uu____3088 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l1 r1 in
                       Prims.op_Negation uu____3088 in
                     if uu____3087
                     then
                       let uu____3090 = FStar_Syntax_Print.term_to_string l1 in
                       let uu____3091 = FStar_Syntax_Print.term_to_string r1 in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____3090 uu____3091
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____3095) ->
                     let uu____3106 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____3106))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___103_3122 = ps in
              {
                main_context = (uu___103_3122.main_context);
                main_goal = (uu___103_3122.main_goal);
                all_implicits = (uu___103_3122.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___103_3122.smt_goals)
              })
       | uu____3123 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___104_3134 = ps in
              {
                main_context = (uu___104_3134.main_context);
                main_goal = (uu___104_3134.main_goal);
                all_implicits = (uu___104_3134.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___104_3134.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____3139 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____3172 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____3172 with
         | (t1,typ,guard) ->
             let uu____3182 = FStar_Syntax_Util.head_and_args typ in
             (match uu____3182 with
              | (hd1,args) ->
                  let uu____3211 =
                    let uu____3219 =
                      let uu____3220 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____3220.FStar_Syntax_Syntax.n in
                    (uu____3219, args) in
                  (match uu____3211 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____3233)::(q,uu____3235)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.or_lid
                       ->
                       let v_p =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None p in
                       let v_q =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None q in
                       let g1 =
                         let uu___105_3264 = g in
                         let uu____3265 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____3265;
                           witness = (uu___105_3264.witness);
                           goal_ty = (uu___105_3264.goal_ty);
                           opts = (uu___105_3264.opts)
                         } in
                       let g2 =
                         let uu___106_3267 = g in
                         let uu____3268 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____3268;
                           witness = (uu___106_3267.witness);
                           goal_ty = (uu___106_3267.goal_ty);
                           opts = (uu___106_3267.opts)
                         } in
                       bind dismiss
                         (fun uu____3273  ->
                            let uu____3274 = add_goals [g1; g2] in
                            bind uu____3274
                              (fun uu____3280  ->
                                 let uu____3281 =
                                   let uu____3284 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____3285 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____3284, uu____3285) in
                                 ret uu____3281))
                   | uu____3288 ->
                       let uu____3296 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____3296)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____3315 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____3315);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___107_3321 = g in
                 {
                   context = (uu___107_3321.context);
                   witness = (uu___107_3321.witness);
                   goal_ty = (uu___107_3321.goal_ty);
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
      FStar_Syntax_Syntax.syntax ->
      (proofstate,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____3349 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____3349 with
      | (u,uu____3359,g_u) ->
          let g =
            let uu____3368 = FStar_Options.peek () in
            { context = env; witness = u; goal_ty = typ; opts = uu____3368 } in
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            } in
          (ps, u)