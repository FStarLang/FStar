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
                                  let uu___94_1297 = goal in
                                  let uu____1298 = bnorm env' u in
                                  let uu____1299 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1298;
                                    goal_ty = uu____1299;
                                    opts = (uu___94_1297.opts)
                                  } in
                                replace_cur uu____1296 in
                              bind uu____1294 (fun uu____1303  -> ret b1)
                            else fail "intro: unification failed")))
       | FStar_Pervasives_Native.None  ->
           let uu____1311 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1311)
let intro_rec:
  (FStar_Syntax_Syntax.binder,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 tac
  =
  bind cur_goal
    (fun goal  ->
       FStar_Util.print_string
         "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
       FStar_Util.print_string
         "WARNING (intro_rec): proceed at your own risk...\n";
       (let uu____1337 = FStar_Syntax_Util.arrow_one goal.goal_ty in
        match uu____1337 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1350 = FStar_Syntax_Subst.open_comp [b] c in
            (match uu____1350 with
             | (bs,c1) ->
                 let b1 =
                   match bs with
                   | b1::[] -> b1
                   | uu____1372 ->
                       failwith
                         "impossible: open_comp returned different amount of binders" in
                 let uu____1375 =
                   let uu____1376 = FStar_Syntax_Util.is_total_comp c1 in
                   Prims.op_Negation uu____1376 in
                 if uu____1375
                 then fail "Codomain is effectful"
                 else
                   (let bv =
                      FStar_Syntax_Syntax.gen_bv "__recf"
                        FStar_Pervasives_Native.None goal.goal_ty in
                    let bs1 =
                      let uu____1390 = FStar_Syntax_Syntax.mk_binder bv in
                      [uu____1390; b1] in
                    let env' =
                      FStar_TypeChecker_Env.push_binders goal.context bs1 in
                    let uu____1396 =
                      let uu____1400 = comp_to_typ c1 in
                      new_uvar env' uu____1400 in
                    bind uu____1396
                      (fun uu____1419  ->
                         match uu____1419 with
                         | (u,g) ->
                             let lb =
                               let uu____1430 =
                                 FStar_Syntax_Util.abs [b1] u
                                   FStar_Pervasives_Native.None in
                               FStar_Syntax_Util.mk_letbinding
                                 (FStar_Util.Inl bv) [] goal.goal_ty
                                 FStar_Parser_Const.effect_Tot_lid uu____1430 in
                             let body = FStar_Syntax_Syntax.bv_to_name bv in
                             let uu____1438 =
                               FStar_Syntax_Subst.close_let_rec [lb] body in
                             (match uu____1438 with
                              | (lbs,body1) ->
                                  let tm =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((true, lbs), body1))
                                      FStar_Pervasives_Native.None
                                      (goal.witness).FStar_Syntax_Syntax.pos in
                                  (FStar_Util.print_string
                                     "calling teq_nosmt\n";
                                   (let res =
                                      FStar_TypeChecker_Rel.teq_nosmt
                                        goal.context goal.witness tm in
                                    if res
                                    then
                                      let uu____1469 =
                                        let uu____1471 =
                                          let uu___95_1472 = goal in
                                          let uu____1473 = bnorm env' u in
                                          let uu____1474 =
                                            let uu____1475 = comp_to_typ c1 in
                                            bnorm env' uu____1475 in
                                          {
                                            context = env';
                                            witness = uu____1473;
                                            goal_ty = uu____1474;
                                            opts = (uu___95_1472.opts)
                                          } in
                                        replace_cur uu____1471 in
                                      bind uu____1469
                                        (fun uu____1482  ->
                                           let uu____1483 =
                                             let uu____1488 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 bv in
                                             (uu____1488, b1) in
                                           ret uu____1483)
                                    else fail "intro_rec: unification failed"))))))
        | FStar_Pervasives_Native.None  ->
            let uu____1502 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1502))
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
           let uu____1529 =
             let uu____1531 = FStar_List.map tr s in
             FStar_List.flatten uu____1531 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1529 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___96_1539 = goal in
            {
              context = (uu___96_1539.context);
              witness = w;
              goal_ty = t;
              opts = (uu___96_1539.opts)
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
       let uu____1556 = istrivial goal.context goal.goal_ty in
       if uu____1556
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____1560 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1560))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1570 =
           try
             let uu____1586 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1586
           with
           | e ->
               let uu____1603 = FStar_Syntax_Print.term_to_string t in
               let uu____1604 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1603
                 uu____1604 in
         bind uu____1570
           (fun uu____1616  ->
              match uu____1616 with
              | (t1,typ,guard) ->
                  let uu____1624 =
                    let uu____1625 =
                      let uu____1626 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1626 in
                    Prims.op_Negation uu____1625 in
                  if uu____1624
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1629 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1629
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1633 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1634 =
                          let uu____1635 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1635 in
                        let uu____1636 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1633 uu____1634 uu____1636))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1646 =
           try
             let uu____1662 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1662
           with
           | e ->
               let uu____1679 = FStar_Syntax_Print.term_to_string t in
               let uu____1680 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1679
                 uu____1680 in
         bind uu____1646
           (fun uu____1692  ->
              match uu____1692 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1705 =
                       let uu____1706 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1706 in
                     if uu____1705
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1709 =
                          let uu____1716 =
                            let uu____1722 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1722.FStar_Syntax_Syntax.effect_args in
                          match uu____1716 with
                          | pre::post::uu____1731 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____1761 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1709 with
                        | (pre,post) ->
                            let uu____1784 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1784
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1788  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____1790 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1791 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1792 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1790 uu____1791 uu____1792)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1803 =
          let uu____1807 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1807 in
        FStar_List.map FStar_Pervasives_Native.fst uu____1803 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1836 = let uu____1839 = exact tm in trytac uu____1839 in
           bind uu____1836
             (fun r  ->
                match r with
                | FStar_Pervasives_Native.Some r1 -> ret ()
                | FStar_Pervasives_Native.None  ->
                    let uu____1848 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1848 with
                     | (tm1,typ,guard) ->
                         let uu____1856 =
                           let uu____1857 =
                             let uu____1858 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1858 in
                           Prims.op_Negation uu____1857 in
                         if uu____1856
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1861 = FStar_Syntax_Util.arrow_one typ in
                            match uu____1861 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____1868 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1868
                            | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                let uu____1878 =
                                  let uu____1879 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____1879 in
                                if uu____1878
                                then fail "apply: not total"
                                else
                                  (let uu____1882 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____1882
                                     (fun uu____1893  ->
                                        match uu____1893 with
                                        | (u,g_u) ->
                                            let tm' =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                tm1 [(u, aq)]
                                                FStar_Pervasives_Native.None
                                                (goal.context).FStar_TypeChecker_Env.range in
                                            let uu____1908 = __apply uopt tm' in
                                            bind uu____1908
                                              (fun uu____1914  ->
                                                 let uu____1915 =
                                                   let uu____1916 =
                                                     let uu____1919 =
                                                       let uu____1920 =
                                                         FStar_Syntax_Util.head_and_args
                                                           u in
                                                       FStar_Pervasives_Native.fst
                                                         uu____1920 in
                                                     FStar_Syntax_Subst.compress
                                                       uu____1919 in
                                                   uu____1916.FStar_Syntax_Syntax.n in
                                                 match uu____1915 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     (uvar,uu____1939) ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1959 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____1959
                                                          then ret ()
                                                          else
                                                            (let uu____1962 =
                                                               let uu____1964
                                                                 =
                                                                 let uu____1965
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____1966
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1965;
                                                                   goal_ty =
                                                                    uu____1966;
                                                                   opts =
                                                                    (goal.opts)
                                                                 } in
                                                               [uu____1964] in
                                                             add_goals
                                                               uu____1962))
                                                 | uu____1967 -> ret ())))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1974 = __apply true tm in focus uu____1974
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1989 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1989 with
         | (tm1,t,guard) ->
             let uu____1997 =
               let uu____1998 =
                 let uu____1999 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1999 in
               Prims.op_Negation uu____1998 in
             if uu____1997
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____2002 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____2002 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2019 =
                         FStar_List.fold_left
                           (fun uu____2049  ->
                              fun uu____2050  ->
                                match (uu____2049, uu____2050) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2099 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____2099 with
                                     | (u,uu____2114,g_u) ->
                                         let uu____2122 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____2122,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____2019 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____2154 =
                             let uu____2161 =
                               let uu____2167 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____2167.FStar_Syntax_Syntax.effect_args in
                             match uu____2161 with
                             | pre::post::uu____2176 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____2206 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____2154 with
                            | (pre,post) ->
                                let uu____2229 =
                                  let uu____2231 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____2231 goal.goal_ty in
                                (match uu____2229 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____2233 =
                                       let uu____2234 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____2234 in
                                     let uu____2235 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____2233 uu____2235
                                 | FStar_Pervasives_Native.Some g ->
                                     let uu____2237 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         goal.context g in
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____2283  ->
                                               match uu____2283 with
                                               | (uu____2290,uu____2291,uu____2292,tm2,uu____2294,uu____2295)
                                                   ->
                                                   let uu____2296 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____2296 with
                                                    | (hd1,uu____2307) ->
                                                        let uu____2322 =
                                                          let uu____2323 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____2323.FStar_Syntax_Syntax.n in
                                                        (match uu____2322
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____2326 ->
                                                             true
                                                         | uu____2337 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____2347  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____2357 =
                                                 let uu____2361 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____2361 in
                                               FStar_List.map
                                                 FStar_Pervasives_Native.fst
                                                 uu____2357 in
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
                                             let uu____2391 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____2391 with
                                             | (hd1,uu____2402) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____2418) ->
                                                      appears uv goals
                                                  | uu____2435 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____2461  ->
                                                     match uu____2461 with
                                                     | (_msg,_env,_uvar,term,typ,uu____2473)
                                                         ->
                                                         let uu____2474 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____2475 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____2474;
                                                           goal_ty =
                                                             uu____2475;
                                                           opts = (goal.opts)
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____2507 = f x xs1 in
                                                 if uu____2507
                                                 then
                                                   let uu____2509 =
                                                     filter' f xs1 in
                                                   x :: uu____2509
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____2520 =
                                                      checkone g1.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____2520) sub_goals in
                                           let uu____2521 =
                                             add_irrelevant_goal goal.context
                                               pre goal.opts in
                                           bind uu____2521
                                             (fun uu____2525  ->
                                                let uu____2526 =
                                                  trytac trivial in
                                                bind uu____2526
                                                  (fun uu____2532  ->
                                                     let uu____2534 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits in
                                                     bind uu____2534
                                                       (fun uu____2537  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2547 =
           FStar_All.pipe_left mlog
             (fun uu____2555  ->
                let uu____2556 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____2557 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2556
                  uu____2557) in
         bind uu____2547
           (fun uu____2569  ->
              let uu____2570 =
                let uu____2572 =
                  let uu____2573 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____2573 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2572 in
              match uu____2570 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2580::(x,uu____2582)::(e,uu____2584)::[])) when
                  FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
                  let uu____2618 =
                    let uu____2619 = FStar_Syntax_Subst.compress x in
                    uu____2619.FStar_Syntax_Syntax.n in
                  (match uu____2618 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___101_2625 = goal in
                         let uu____2626 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2629 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___101_2625.context);
                           witness = uu____2626;
                           goal_ty = uu____2629;
                           opts = (uu___101_2625.opts)
                         } in
                       replace_cur goal1
                   | uu____2632 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2633 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2639 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2639 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2654 = FStar_Util.set_mem x fns_ty in
           if uu____2654
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2657 = new_uvar env' goal.goal_ty in
              bind uu____2657
                (fun uu____2667  ->
                   match uu____2667 with
                   | (u,g) ->
                       let uu____2673 =
                         let uu____2674 =
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness u in
                         Prims.op_Negation uu____2674 in
                       if uu____2673
                       then fail "clear: unification failed"
                       else
                         (let new_goal =
                            let uu___102_2678 = goal in
                            let uu____2679 = bnorm env' u in
                            {
                              context = env';
                              witness = uu____2679;
                              goal_ty = (uu___102_2678.goal_ty);
                              opts = (uu___102_2678.opts)
                            } in
                          bind dismiss
                            (fun uu____2681  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2691 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2691 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2708 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2708 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____2722 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____2722 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___103_2742 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___103_2742.opts)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2752 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2752 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2764 = FStar_Syntax_Print.bv_to_string x in
               let uu____2765 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2764 uu____2765
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2778 = revert_all_hd xs1 in
        bind uu____2778 (fun uu____2781  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___104_2796 = g in
           {
             context = ctx';
             witness = (uu___104_2796.witness);
             goal_ty = (uu___104_2796.goal_ty);
             opts = (uu___104_2796.opts)
           } in
         bind dismiss (fun uu____2798  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___105_2813 = g in
           {
             context = ctx';
             witness = (uu___105_2813.witness);
             goal_ty = (uu___105_2813.goal_ty);
             opts = (uu___105_2813.opts)
           } in
         bind dismiss (fun uu____2815  -> add_goals [g']))
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2849 = f x in
      bind uu____2849
        (fun y  ->
           let uu____2855 = mapM f xs in
           bind uu____2855 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2891 = FStar_Syntax_Subst.compress t in
          uu____2891.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2917 = ff hd1 in
              bind uu____2917
                (fun hd2  ->
                   let fa uu____2931 =
                     match uu____2931 with
                     | (a,q) ->
                         let uu____2939 = ff a in
                         bind uu____2939 (fun a1  -> ret (a1, q)) in
                   let uu____2947 = mapM fa args in
                   bind uu____2947
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2982 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2982 with
               | (bs1,t') ->
                   let uu____2988 =
                     let uu____2990 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2990 t' in
                   bind uu____2988
                     (fun t''  ->
                        let uu____2994 =
                          let uu____2995 =
                            let uu____3005 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____3006 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____3005, uu____3006, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2995 in
                        ret uu____2994))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____3020 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___106_3024 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___106_3024.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___106_3024.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___106_3024.FStar_Syntax_Syntax.vars)
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
            let uu____3053 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____3053 with
            | (t1,lcomp,g) ->
                let uu____3061 =
                  (let uu____3064 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____3064) ||
                    (let uu____3066 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____3066) in
                if uu____3061
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____3072 = new_uvar env typ in
                   bind uu____3072
                     (fun uu____3083  ->
                        match uu____3083 with
                        | (ut,guard) ->
                            (log ps
                               (fun uu____3093  ->
                                  let uu____3094 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  let uu____3095 =
                                    FStar_Syntax_Print.term_to_string ut in
                                  FStar_Util.print2
                                    "Pointwise_rec: making equality %s = %s\n"
                                    uu____3094 uu____3095);
                             (let uu____3096 =
                                let uu____3098 =
                                  let uu____3099 =
                                    FStar_TypeChecker_TcTerm.universe_of env
                                      typ in
                                  FStar_Syntax_Util.mk_eq2 uu____3099 typ t1
                                    ut in
                                add_irrelevant_goal env uu____3098 opts in
                              bind uu____3096
                                (fun uu____3102  ->
                                   let uu____3103 =
                                     bind tau
                                       (fun uu____3108  ->
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env guard;
                                          (let ut1 =
                                             FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                               env ut in
                                           ret ut1)) in
                                   focus uu____3103)))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____3126 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____3126 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____3149  ->
                   let uu____3150 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____3150);
              bind dismiss_all
                (fun uu____3153  ->
                   let uu____3154 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____3154
                     (fun gt'  ->
                        log ps
                          (fun uu____3163  ->
                             let uu____3164 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____3164);
                        (let uu____3165 = push_goals gs in
                         bind uu____3165
                           (fun uu____3168  ->
                              add_goals
                                [(let uu___107_3170 = g in
                                  {
                                    context = (uu___107_3170.context);
                                    witness = (uu___107_3170.witness);
                                    goal_ty = gt';
                                    opts = (uu___107_3170.opts)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____3189 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____3189 with
       | FStar_Pervasives_Native.Some t ->
           let uu____3199 = FStar_Syntax_Util.head_and_args' t in
           (match uu____3199 with
            | (hd1,args) ->
                let uu____3220 =
                  let uu____3228 =
                    let uu____3229 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____3229.FStar_Syntax_Syntax.n in
                  (uu____3228, args) in
                (match uu____3220 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3239::(l,uu____3241)::(r,uu____3243)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____3277 =
                       let uu____3278 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____3278 in
                     if uu____3277
                     then
                       let uu____3280 = FStar_Syntax_Print.term_to_string l in
                       let uu____3281 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____3280 uu____3281
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____3285) ->
                     let uu____3296 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____3296))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____3303 = new_uvar g.context g.goal_ty in
       bind uu____3303
         (fun uu____3313  ->
            match uu____3313 with
            | (u,u_g) ->
                let g' =
                  let uu___108_3320 = g in
                  {
                    context = (uu___108_3320.context);
                    witness = u;
                    goal_ty = (uu___108_3320.goal_ty);
                    opts = (uu___108_3320.opts)
                  } in
                bind dismiss
                  (fun uu____3323  ->
                     let uu____3324 =
                       let uu____3326 =
                         let uu____3327 =
                           FStar_TypeChecker_TcTerm.universe_of g.context
                             g.goal_ty in
                         FStar_Syntax_Util.mk_eq2 uu____3327 g.goal_ty u
                           g.witness in
                       add_irrelevant_goal g.context uu____3326 g.opts in
                     bind uu____3324
                       (fun uu____3330  ->
                          let uu____3331 = add_goals [g'] in
                          bind uu____3331 (fun uu____3334  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___109_3348 = ps in
              {
                main_context = (uu___109_3348.main_context);
                main_goal = (uu___109_3348.main_goal);
                all_implicits = (uu___109_3348.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___109_3348.smt_goals)
              })
       | uu____3349 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___110_3360 = ps in
              {
                main_context = (uu___110_3360.main_context);
                main_goal = (uu___110_3360.main_goal);
                all_implicits = (uu___110_3360.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___110_3360.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____3365 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____3398 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____3398 with
         | (t1,typ,guard) ->
             let uu____3408 = FStar_Syntax_Util.head_and_args typ in
             (match uu____3408 with
              | (hd1,args) ->
                  let uu____3437 =
                    let uu____3445 =
                      let uu____3446 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____3446.FStar_Syntax_Syntax.n in
                    (uu____3445, args) in
                  (match uu____3437 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____3459)::(q,uu____3461)::[]) when
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
                         let uu___111_3490 = g in
                         let uu____3491 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____3491;
                           witness = (uu___111_3490.witness);
                           goal_ty = (uu___111_3490.goal_ty);
                           opts = (uu___111_3490.opts)
                         } in
                       let g2 =
                         let uu___112_3493 = g in
                         let uu____3494 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____3494;
                           witness = (uu___112_3493.witness);
                           goal_ty = (uu___112_3493.goal_ty);
                           opts = (uu___112_3493.opts)
                         } in
                       bind dismiss
                         (fun uu____3499  ->
                            let uu____3500 = add_goals [g1; g2] in
                            bind uu____3500
                              (fun uu____3506  ->
                                 let uu____3507 =
                                   let uu____3510 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____3511 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____3510, uu____3511) in
                                 ret uu____3507))
                   | uu____3514 ->
                       let uu____3522 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____3522)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____3541 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____3541);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___113_3547 = g in
                 {
                   context = (uu___113_3547.context);
                   witness = (uu___113_3547.witness);
                   goal_ty = (uu___113_3547.goal_ty);
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
      let uu____3575 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____3575 with
      | (u,uu____3585,g_u) ->
          let g =
            let uu____3594 = FStar_Options.peek () in
            { context = env; witness = u; goal_ty = typ; opts = uu____3594 } in
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            } in
          (ps, u)