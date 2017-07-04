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
         let uu___82_729 = p in
         let uu____730 = FStar_List.tl p.goals in
         {
           main_context = (uu___82_729.main_context);
           main_goal = (uu___82_729.main_goal);
           all_implicits = (uu___82_729.all_implicits);
           goals = uu____730;
           smt_goals = (uu___82_729.smt_goals)
         } in
       set uu____728)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___83_737 = p in
          {
            main_context = (uu___83_737.main_context);
            main_goal = (uu___83_737.main_goal);
            all_implicits = (uu___83_737.all_implicits);
            goals = [];
            smt_goals = (uu___83_737.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_750 = p in
            {
              main_context = (uu___84_750.main_context);
              main_goal = (uu___84_750.main_goal);
              all_implicits = (uu___84_750.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___84_750.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___85_763 = p in
            {
              main_context = (uu___85_763.main_context);
              main_goal = (uu___85_763.main_goal);
              all_implicits = (uu___85_763.all_implicits);
              goals = (uu___85_763.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___86_776 = p in
            {
              main_context = (uu___86_776.main_context);
              main_goal = (uu___86_776.main_goal);
              all_implicits = (uu___86_776.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___86_776.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___87_789 = p in
            {
              main_context = (uu___87_789.main_context);
              main_goal = (uu___87_789.main_goal);
              all_implicits = (uu___87_789.all_implicits);
              goals = (uu___87_789.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____797  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___88_808 = p in
            {
              main_context = (uu___88_808.main_context);
              main_goal = (uu___88_808.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___88_808.goals);
              smt_goals = (uu___88_808.smt_goals)
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
                  let uu___89_1057 = p in
                  {
                    main_context = (uu___89_1057.main_context);
                    main_goal = (uu___89_1057.main_goal);
                    all_implicits = (uu___89_1057.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___90_1059 = p in
                  {
                    main_context = (uu___90_1059.main_context);
                    main_goal = (uu___90_1059.main_goal);
                    all_implicits = (uu___90_1059.all_implicits);
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
                                                let uu___91_1092 = p in
                                                {
                                                  main_context =
                                                    (uu___91_1092.main_context);
                                                  main_goal =
                                                    (uu___91_1092.main_goal);
                                                  all_implicits =
                                                    (uu___91_1092.all_implicits);
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
       | uu____1146::uu____1147 ->
           let uu____1149 =
             let uu____1154 = map tau in
             divide (Prims.parse_int "1") tau uu____1154 in
           bind uu____1149
             (fun uu____1165  ->
                match uu____1165 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1190 =
        bind t1
          (fun uu____1194  ->
             let uu____1195 = map t2 in
             bind uu____1195 (fun uu____1200  -> ret ())) in
      focus uu____1190
let intro:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 tac
  =
  bind cur_goal
    (fun goal  ->
       let uu____1217 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1217 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1228 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1228 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1248 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1251 =
                  let uu____1252 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1252 in
                if uu____1251
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1265 = new_uvar env' typ' in
                   bind uu____1265
                     (fun uu____1278  ->
                        match uu____1278 with
                        | (u,g) ->
                            let uu____1286 =
                              let uu____1287 =
                                FStar_Syntax_Util.abs [b1] u
                                  FStar_Pervasives_Native.None in
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                goal.witness uu____1287 in
                            if uu____1286
                            then
                              let uu____1295 =
                                let uu____1297 =
                                  let uu___94_1298 = goal in
                                  let uu____1299 = bnorm env' u in
                                  let uu____1300 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1299;
                                    goal_ty = uu____1300;
                                    opts = (uu___94_1298.opts)
                                  } in
                                replace_cur uu____1297 in
                              bind uu____1295 (fun uu____1304  -> ret b1)
                            else fail "intro: unification failed")))
       | FStar_Pervasives_Native.None  ->
           let uu____1312 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1312)
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
           let uu____1337 =
             let uu____1339 = FStar_List.map tr s in
             FStar_List.flatten uu____1339 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1337 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___95_1347 = goal in
            {
              context = (uu___95_1347.context);
              witness = w;
              goal_ty = t;
              opts = (uu___95_1347.opts)
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
       let uu____1364 = istrivial goal.context goal.goal_ty in
       if uu____1364
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____1368 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1368))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1378 =
           try
             let uu____1394 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1394
           with
           | e ->
               let uu____1411 = FStar_Syntax_Print.term_to_string t in
               let uu____1412 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1411
                 uu____1412 in
         bind uu____1378
           (fun uu____1424  ->
              match uu____1424 with
              | (t1,typ,guard) ->
                  let uu____1432 =
                    let uu____1433 =
                      let uu____1434 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1434 in
                    Prims.op_Negation uu____1433 in
                  if uu____1432
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1437 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1437
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1441 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1442 =
                          let uu____1443 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1443 in
                        let uu____1444 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1441 uu____1442 uu____1444))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1454 =
           try
             let uu____1470 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1470
           with
           | e ->
               let uu____1487 = FStar_Syntax_Print.term_to_string t in
               let uu____1488 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1487
                 uu____1488 in
         bind uu____1454
           (fun uu____1500  ->
              match uu____1500 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1513 =
                       let uu____1514 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1514 in
                     if uu____1513
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1517 =
                          let uu____1524 =
                            let uu____1530 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1530.FStar_Syntax_Syntax.effect_args in
                          match uu____1524 with
                          | pre::post::uu____1539 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____1569 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1517 with
                        | (pre,post) ->
                            let uu____1592 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1592
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1596  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____1598 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1599 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1600 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1598 uu____1599 uu____1600)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1611 =
          let uu____1615 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1615 in
        FStar_List.map FStar_Pervasives_Native.fst uu____1611 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1644 = let uu____1647 = exact tm in trytac uu____1647 in
           bind uu____1644
             (fun r  ->
                match r with
                | FStar_Pervasives_Native.Some r1 -> ret ()
                | FStar_Pervasives_Native.None  ->
                    let uu____1656 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1656 with
                     | (tm1,typ,guard) ->
                         let uu____1664 =
                           let uu____1665 =
                             let uu____1666 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1666 in
                           Prims.op_Negation uu____1665 in
                         if uu____1664
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1669 = FStar_Syntax_Util.arrow_one typ in
                            match uu____1669 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____1676 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1676
                            | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                let uu____1686 =
                                  let uu____1687 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____1687 in
                                if uu____1686
                                then fail "apply: not total"
                                else
                                  (let uu____1690 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____1690
                                     (fun uu____1701  ->
                                        match uu____1701 with
                                        | (u,g_u) ->
                                            let tm' =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                tm1 [(u, aq)]
                                                FStar_Pervasives_Native.None
                                                (goal.context).FStar_TypeChecker_Env.range in
                                            let uu____1716 = __apply uopt tm' in
                                            bind uu____1716
                                              (fun uu____1722  ->
                                                 let uu____1723 =
                                                   let uu____1724 =
                                                     let uu____1727 =
                                                       let uu____1728 =
                                                         FStar_Syntax_Util.head_and_args
                                                           u in
                                                       FStar_Pervasives_Native.fst
                                                         uu____1728 in
                                                     FStar_Syntax_Subst.compress
                                                       uu____1727 in
                                                   uu____1724.FStar_Syntax_Syntax.n in
                                                 match uu____1723 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     (uvar,uu____1747) ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1767 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____1767
                                                          then ret ()
                                                          else
                                                            (let uu____1770 =
                                                               let uu____1772
                                                                 =
                                                                 let uu____1773
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____1774
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1773;
                                                                   goal_ty =
                                                                    uu____1774;
                                                                   opts =
                                                                    (goal.opts)
                                                                 } in
                                                               [uu____1772] in
                                                             add_goals
                                                               uu____1770))
                                                 | uu____1775 -> ret ())))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1782 = __apply true tm in focus uu____1782
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1797 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1797 with
         | (tm1,t,guard) ->
             let uu____1805 =
               let uu____1806 =
                 let uu____1807 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1807 in
               Prims.op_Negation uu____1806 in
             if uu____1805
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1810 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____1810 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____1827 =
                         FStar_List.fold_left
                           (fun uu____1857  ->
                              fun uu____1858  ->
                                match (uu____1857, uu____1858) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____1907 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____1907 with
                                     | (u,uu____1922,g_u) ->
                                         let uu____1930 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____1930,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____1827 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1962 =
                             let uu____1969 =
                               let uu____1975 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____1975.FStar_Syntax_Syntax.effect_args in
                             match uu____1969 with
                             | pre::post::uu____1984 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____2014 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____1962 with
                            | (pre,post) ->
                                let uu____2037 =
                                  let uu____2039 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____2039 goal.goal_ty in
                                (match uu____2037 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____2041 =
                                       let uu____2042 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____2042 in
                                     let uu____2043 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____2041 uu____2043
                                 | FStar_Pervasives_Native.Some g ->
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____2090  ->
                                               match uu____2090 with
                                               | (uu____2097,uu____2098,uu____2099,tm2,uu____2101,uu____2102)
                                                   ->
                                                   let uu____2103 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____2103 with
                                                    | (hd1,uu____2114) ->
                                                        let uu____2129 =
                                                          let uu____2130 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____2130.FStar_Syntax_Syntax.n in
                                                        (match uu____2129
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____2133 ->
                                                             true
                                                         | uu____2144 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____2154  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____2164 =
                                                 let uu____2168 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____2168 in
                                               FStar_List.map
                                                 FStar_Pervasives_Native.fst
                                                 uu____2164 in
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
                                             let uu____2198 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____2198 with
                                             | (hd1,uu____2209) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____2225) ->
                                                      appears uv goals
                                                  | uu____2242 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____2268  ->
                                                     match uu____2268 with
                                                     | (_msg,_env,_uvar,term,typ,uu____2280)
                                                         ->
                                                         let uu____2281 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____2282 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____2281;
                                                           goal_ty =
                                                             uu____2282;
                                                           opts = (goal.opts)
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____2314 = f x xs1 in
                                                 if uu____2314
                                                 then
                                                   let uu____2316 =
                                                     filter' f xs1 in
                                                   x :: uu____2316
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____2327 =
                                                      checkone g1.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____2327) sub_goals in
                                           let uu____2328 =
                                             add_irrelevant_goal goal.context
                                               pre goal.opts in
                                           bind uu____2328
                                             (fun uu____2332  ->
                                                let uu____2333 =
                                                  trytac trivial in
                                                bind uu____2333
                                                  (fun uu____2339  ->
                                                     let uu____2341 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits in
                                                     bind uu____2341
                                                       (fun uu____2344  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2354 =
           FStar_All.pipe_left mlog
             (fun uu____2362  ->
                let uu____2363 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____2364 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2363
                  uu____2364) in
         bind uu____2354
           (fun uu____2376  ->
              let uu____2377 =
                let uu____2379 =
                  let uu____2380 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____2380 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2379 in
              match uu____2377 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2387::(x,uu____2389)::(e,uu____2391)::[])) when
                  FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
                  let uu____2425 =
                    let uu____2426 = FStar_Syntax_Subst.compress x in
                    uu____2426.FStar_Syntax_Syntax.n in
                  (match uu____2425 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___100_2432 = goal in
                         let uu____2433 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2436 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___100_2432.context);
                           witness = uu____2433;
                           goal_ty = uu____2436;
                           opts = (uu___100_2432.opts)
                         } in
                       replace_cur goal1
                   | uu____2439 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2440 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2446 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2446 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2461 = FStar_Util.set_mem x fns_ty in
           if uu____2461
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2464 = new_uvar env' goal.goal_ty in
              bind uu____2464
                (fun uu____2474  ->
                   match uu____2474 with
                   | (u,g) ->
                       let uu____2480 =
                         let uu____2481 =
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness u in
                         Prims.op_Negation uu____2481 in
                       if uu____2480
                       then fail "clear: unification failed"
                       else
                         (let new_goal =
                            let uu___101_2485 = goal in
                            let uu____2486 = bnorm env' u in
                            {
                              context = env';
                              witness = uu____2486;
                              goal_ty = (uu___101_2485.goal_ty);
                              opts = (uu___101_2485.opts)
                            } in
                          bind dismiss
                            (fun uu____2488  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2498 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2498 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2515 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2515 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____2529 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____2529 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___102_2549 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___102_2549.opts)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2559 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2559 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2571 = FStar_Syntax_Print.bv_to_string x in
               let uu____2572 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2571 uu____2572
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2585 = revert_all_hd xs1 in
        bind uu____2585 (fun uu____2588  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___103_2603 = g in
           {
             context = ctx';
             witness = (uu___103_2603.witness);
             goal_ty = (uu___103_2603.goal_ty);
             opts = (uu___103_2603.opts)
           } in
         bind dismiss (fun uu____2605  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___104_2620 = g in
           {
             context = ctx';
             witness = (uu___104_2620.witness);
             goal_ty = (uu___104_2620.goal_ty);
             opts = (uu___104_2620.opts)
           } in
         bind dismiss (fun uu____2622  -> add_goals [g']))
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2658 = f x in
      bind uu____2658
        (fun y  ->
           let uu____2664 = mapM f xs in
           bind uu____2664 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2700 = FStar_Syntax_Subst.compress t in
          uu____2700.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2726 = ff hd1 in
              bind uu____2726
                (fun hd2  ->
                   let fa uu____2740 =
                     match uu____2740 with
                     | (a,q) ->
                         let uu____2748 = ff a in
                         bind uu____2748 (fun a1  -> ret (a1, q)) in
                   let uu____2756 = mapM fa args in
                   bind uu____2756
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2791 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2791 with
               | (bs1,t') ->
                   let uu____2797 =
                     let uu____2799 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2799 t' in
                   bind uu____2797
                     (fun t''  ->
                        let uu____2803 =
                          let uu____2804 =
                            let uu____2814 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____2815 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____2814, uu____2815, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2804 in
                        ret uu____2803))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2829 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___105_2833 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___105_2833.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___105_2833.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___105_2833.FStar_Syntax_Syntax.vars)
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
            let uu____2862 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____2862 with
            | (t1,lcomp,g) ->
                let uu____2870 =
                  (let uu____2873 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____2873) ||
                    (let uu____2875 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____2875) in
                if uu____2870
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____2881 = new_uvar env typ in
                   bind uu____2881
                     (fun uu____2892  ->
                        match uu____2892 with
                        | (ut,guard) ->
                            (log ps
                               (fun uu____2902  ->
                                  let uu____2903 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  let uu____2904 =
                                    FStar_Syntax_Print.term_to_string ut in
                                  FStar_Util.print2
                                    "Pointwise_rec: making equality %s = %s\n"
                                    uu____2903 uu____2904);
                             (let uu____2905 =
                                let uu____2907 =
                                  let uu____2908 =
                                    FStar_TypeChecker_TcTerm.universe_of env
                                      typ in
                                  FStar_Syntax_Util.mk_eq2 uu____2908 typ t1
                                    ut in
                                add_irrelevant_goal env uu____2907 opts in
                              bind uu____2905
                                (fun uu____2911  ->
                                   let uu____2912 =
                                     bind tau
                                       (fun uu____2917  ->
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env guard;
                                          (let ut1 =
                                             FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                               env ut in
                                           ret ut1)) in
                                   focus uu____2912)))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2935 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2935 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2958  ->
                   let uu____2959 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2959);
              bind dismiss_all
                (fun uu____2962  ->
                   let uu____2963 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____2963
                     (fun gt'  ->
                        log ps
                          (fun uu____2972  ->
                             let uu____2973 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2973);
                        (let uu____2974 = push_goals gs in
                         bind uu____2974
                           (fun uu____2977  ->
                              add_goals
                                [(let uu___106_2979 = g in
                                  {
                                    context = (uu___106_2979.context);
                                    witness = (uu___106_2979.witness);
                                    goal_ty = gt';
                                    opts = (uu___106_2979.opts)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2998 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2998 with
       | FStar_Pervasives_Native.Some t ->
           let uu____3008 = FStar_Syntax_Util.head_and_args' t in
           (match uu____3008 with
            | (hd1,args) ->
                let uu____3029 =
                  let uu____3037 =
                    let uu____3038 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____3038.FStar_Syntax_Syntax.n in
                  (uu____3037, args) in
                (match uu____3029 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3048::(l,uu____3050)::(r,uu____3052)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____3086 =
                       let uu____3087 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____3087 in
                     if uu____3086
                     then
                       let uu____3089 = FStar_Syntax_Print.term_to_string l in
                       let uu____3090 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____3089 uu____3090
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____3094) ->
                     let uu____3105 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____3105))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___107_3121 = ps in
              {
                main_context = (uu___107_3121.main_context);
                main_goal = (uu___107_3121.main_goal);
                all_implicits = (uu___107_3121.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___107_3121.smt_goals)
              })
       | uu____3122 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___108_3133 = ps in
              {
                main_context = (uu___108_3133.main_context);
                main_goal = (uu___108_3133.main_goal);
                all_implicits = (uu___108_3133.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___108_3133.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____3138 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____3171 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____3171 with
         | (t1,typ,guard) ->
             let uu____3181 = FStar_Syntax_Util.head_and_args typ in
             (match uu____3181 with
              | (hd1,args) ->
                  let uu____3210 =
                    let uu____3218 =
                      let uu____3219 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____3219.FStar_Syntax_Syntax.n in
                    (uu____3218, args) in
                  (match uu____3210 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____3232)::(q,uu____3234)::[]) when
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
                         let uu___109_3263 = g in
                         let uu____3264 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____3264;
                           witness = (uu___109_3263.witness);
                           goal_ty = (uu___109_3263.goal_ty);
                           opts = (uu___109_3263.opts)
                         } in
                       let g2 =
                         let uu___110_3266 = g in
                         let uu____3267 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____3267;
                           witness = (uu___110_3266.witness);
                           goal_ty = (uu___110_3266.goal_ty);
                           opts = (uu___110_3266.opts)
                         } in
                       bind dismiss
                         (fun uu____3272  ->
                            let uu____3273 = add_goals [g1; g2] in
                            bind uu____3273
                              (fun uu____3279  ->
                                 let uu____3280 =
                                   let uu____3283 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____3284 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____3283, uu____3284) in
                                 ret uu____3280))
                   | uu____3287 ->
                       let uu____3295 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____3295)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____3314 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____3314);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___111_3320 = g in
                 {
                   context = (uu___111_3320.context);
                   witness = (uu___111_3320.witness);
                   goal_ty = (uu___111_3320.goal_ty);
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
      let uu____3348 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____3348 with
      | (u,uu____3358,g_u) ->
          let g =
            let uu____3367 = FStar_Options.peek () in
            { context = env; witness = u; goal_ty = typ; opts = uu____3367 } in
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            } in
          (ps, u)