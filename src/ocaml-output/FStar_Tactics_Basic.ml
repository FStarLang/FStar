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
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____420) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____426) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: goal -> Prims.bool =
  fun g  ->
    let uu____436 =
      let uu____439 =
        FStar_TypeChecker_Normalize.unfold_whnf g.context g.goal_ty in
      FStar_Syntax_Util.un_squash uu____439 in
    match uu____436 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____443 -> false
let dump_goal ps goal =
  let uu____462 = goal_to_string goal in tacprint uu____462
let dump_cur: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____472 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____475 = FStar_List.hd ps.goals in dump_goal ps uu____475))
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____487 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____487);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____496 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____496);
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
      let uu____545 = FStar_ST.read tac_verb_dbg in
      match uu____545 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____551 =
              let uu____553 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              FStar_Pervasives_Native.Some uu____553 in
            FStar_ST.write tac_verb_dbg uu____551);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____586 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____586
        then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
        else ());
       Failed (msg, ps))
let fail1 msg x = let uu____604 = FStar_Util.format1 msg x in fail uu____604
let fail2 msg x y =
  let uu____627 = FStar_Util.format2 msg x y in fail uu____627
let fail3 msg x y z =
  let uu____656 = FStar_Util.format3 msg x y z in fail uu____656
let trytac t =
  mk_tac
    (fun ps  ->
       let tx = FStar_Syntax_Unionfind.new_transaction () in
       let uu____679 = run t ps in
       match uu____679 with
       | Success (a,q) ->
           (FStar_Syntax_Unionfind.commit tx;
            Success ((FStar_Pervasives_Native.Some a), q))
       | Failed (uu____688,uu____689) ->
           (FStar_Syntax_Unionfind.rollback tx;
            Success (FStar_Pervasives_Native.None, ps)))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____700  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____709 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____709
      then ()
      else
        (let uu____711 =
           let uu____712 =
             let uu____713 = FStar_Syntax_Print.term_to_string solution in
             let uu____714 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____715 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____713
               uu____714 uu____715 in
           TacFailure uu____712 in
         raise uu____711)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____720 =
         let uu___82_721 = p in
         let uu____722 = FStar_List.tl p.goals in
         {
           main_context = (uu___82_721.main_context);
           main_goal = (uu___82_721.main_goal);
           all_implicits = (uu___82_721.all_implicits);
           goals = uu____722;
           smt_goals = (uu___82_721.smt_goals)
         } in
       set uu____720)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___83_729 = p in
          {
            main_context = (uu___83_729.main_context);
            main_goal = (uu___83_729.main_goal);
            all_implicits = (uu___83_729.all_implicits);
            goals = [];
            smt_goals = (uu___83_729.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_742 = p in
            {
              main_context = (uu___84_742.main_context);
              main_goal = (uu___84_742.main_goal);
              all_implicits = (uu___84_742.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___84_742.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___85_755 = p in
            {
              main_context = (uu___85_755.main_context);
              main_goal = (uu___85_755.main_goal);
              all_implicits = (uu___85_755.all_implicits);
              goals = (uu___85_755.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___86_768 = p in
            {
              main_context = (uu___86_768.main_context);
              main_goal = (uu___86_768.main_goal);
              all_implicits = (uu___86_768.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___86_768.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___87_781 = p in
            {
              main_context = (uu___87_781.main_context);
              main_goal = (uu___87_781.main_goal);
              all_implicits = (uu___87_781.all_implicits);
              goals = (uu___87_781.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____789  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___88_800 = p in
            {
              main_context = (uu___88_800.main_context);
              main_goal = (uu___88_800.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___88_800.goals);
              smt_goals = (uu___88_800.smt_goals)
            }))
let new_uvar:
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2 tac
  =
  fun env  ->
    fun typ  ->
      let uu____821 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____821 with
      | (u,uu____832,g_u) ->
          let uu____840 = add_implicits g_u.FStar_TypeChecker_Env.implicits in
          bind uu____840 (fun uu____845  -> ret (u, g_u))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____852 = FStar_Syntax_Util.un_squash t in
    match uu____852 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____858 =
          let uu____859 = FStar_Syntax_Subst.compress t' in
          uu____859.FStar_Syntax_Syntax.n in
        (match uu____858 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____862 -> false)
    | uu____863 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____870 = FStar_Syntax_Util.un_squash t in
    match uu____870 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____876 =
          let uu____877 = FStar_Syntax_Subst.compress t' in
          uu____877.FStar_Syntax_Syntax.n in
        (match uu____876 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____880 -> false)
    | uu____881 -> false
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
        let uu____907 = new_uvar env typ in
        bind uu____907
          (fun uu____917  ->
             match uu____917 with
             | (u,g_u) ->
                 let goal =
                   { context = env; witness = u; goal_ty = typ; opts } in
                 add_goals [goal])
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____928 = is_irrelevant g in
       if uu____928
       then bind dismiss (fun uu____931  -> add_smt_goals [g])
       else
         (let uu____933 = FStar_Syntax_Print.term_to_string g.goal_ty in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____933))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____970 =
         try let uu____989 = FStar_List.splitAt n1 p.goals in ret uu____989
         with | uu____1006 -> fail "divide: not enough goals" in
       bind uu____970
         (fun uu____1023  ->
            match uu____1023 with
            | (lgs,rgs) ->
                let lp =
                  let uu___89_1038 = p in
                  {
                    main_context = (uu___89_1038.main_context);
                    main_goal = (uu___89_1038.main_goal);
                    all_implicits = (uu___89_1038.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___90_1040 = p in
                  {
                    main_context = (uu___90_1040.main_context);
                    main_goal = (uu___90_1040.main_goal);
                    all_implicits = (uu___90_1040.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____1041 = set lp in
                bind uu____1041
                  (fun uu____1046  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____1056 = set rp in
                               bind uu____1056
                                 (fun uu____1061  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___91_1073 = p in
                                                {
                                                  main_context =
                                                    (uu___91_1073.main_context);
                                                  main_goal =
                                                    (uu___91_1073.main_goal);
                                                  all_implicits =
                                                    (uu___91_1073.all_implicits);
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
                                              let uu____1074 = set p' in
                                              bind uu____1074
                                                (fun uu____1079  ->
                                                   ret (a, b))))))))))
let focus f =
  let uu____1094 = divide (Prims.parse_int "1") f idtac in
  bind uu____1094
    (fun uu____1102  -> match uu____1102 with | (a,()) -> ret a)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____1126::uu____1127 ->
           let uu____1129 =
             let uu____1134 = map tau in
             divide (Prims.parse_int "1") tau uu____1134 in
           bind uu____1129
             (fun uu____1145  ->
                match uu____1145 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1170 =
        bind t1
          (fun uu____1174  ->
             let uu____1175 = map t2 in
             bind uu____1175 (fun uu____1180  -> ret ())) in
      focus uu____1170
let intro:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 tac
  =
  bind cur_goal
    (fun goal  ->
       let uu____1197 = FStar_Syntax_Util.arrow_one goal.goal_ty in
       match uu____1197 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1208 = FStar_Syntax_Subst.open_comp [b] c in
           (match uu____1208 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1228 ->
                      failwith
                        "impossible: open_comp returned different amount of binders" in
                let uu____1231 =
                  let uu____1232 = FStar_Syntax_Util.is_total_comp c1 in
                  Prims.op_Negation uu____1232 in
                if uu____1231
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1] in
                   let typ' = comp_to_typ c1 in
                   let uu____1245 = new_uvar env' typ' in
                   bind uu____1245
                     (fun uu____1258  ->
                        match uu____1258 with
                        | (u,g) ->
                            let uu____1266 =
                              let uu____1267 =
                                FStar_Syntax_Util.abs [b1] u
                                  FStar_Pervasives_Native.None in
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                goal.witness uu____1267 in
                            if uu____1266
                            then
                              let uu____1275 =
                                let uu____1277 =
                                  let uu___94_1278 = goal in
                                  let uu____1279 = bnorm env' u in
                                  let uu____1280 = bnorm env' typ' in
                                  {
                                    context = env';
                                    witness = uu____1279;
                                    goal_ty = uu____1280;
                                    opts = (uu___94_1278.opts)
                                  } in
                                replace_cur uu____1277 in
                              bind uu____1275 (fun uu____1284  -> ret b1)
                            else fail "intro: unification failed")))
       | FStar_Pervasives_Native.None  ->
           let uu____1292 = FStar_Syntax_Print.term_to_string goal.goal_ty in
           fail1 "intro: goal is not an arrow (%s)" uu____1292)
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
       (let uu____1318 = FStar_Syntax_Util.arrow_one goal.goal_ty in
        match uu____1318 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1331 = FStar_Syntax_Subst.open_comp [b] c in
            (match uu____1331 with
             | (bs,c1) ->
                 let b1 =
                   match bs with
                   | b1::[] -> b1
                   | uu____1353 ->
                       failwith
                         "impossible: open_comp returned different amount of binders" in
                 let uu____1356 =
                   let uu____1357 = FStar_Syntax_Util.is_total_comp c1 in
                   Prims.op_Negation uu____1357 in
                 if uu____1356
                 then fail "Codomain is effectful"
                 else
                   (let bv =
                      FStar_Syntax_Syntax.gen_bv "__recf"
                        FStar_Pervasives_Native.None goal.goal_ty in
                    let bs1 =
                      let uu____1371 = FStar_Syntax_Syntax.mk_binder bv in
                      [uu____1371; b1] in
                    let env' =
                      FStar_TypeChecker_Env.push_binders goal.context bs1 in
                    let uu____1377 =
                      let uu____1381 = comp_to_typ c1 in
                      new_uvar env' uu____1381 in
                    bind uu____1377
                      (fun uu____1400  ->
                         match uu____1400 with
                         | (u,g) ->
                             let lb =
                               let uu____1411 =
                                 FStar_Syntax_Util.abs [b1] u
                                   FStar_Pervasives_Native.None in
                               FStar_Syntax_Util.mk_letbinding
                                 (FStar_Util.Inl bv) [] goal.goal_ty
                                 FStar_Parser_Const.effect_Tot_lid uu____1411 in
                             let body = FStar_Syntax_Syntax.bv_to_name bv in
                             let uu____1418 =
                               FStar_Syntax_Subst.close_let_rec [lb] body in
                             (match uu____1418 with
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
                                      let uu____1447 =
                                        let uu____1449 =
                                          let uu___95_1450 = goal in
                                          let uu____1451 = bnorm env' u in
                                          let uu____1452 =
                                            let uu____1453 = comp_to_typ c1 in
                                            bnorm env' uu____1453 in
                                          {
                                            context = env';
                                            witness = uu____1451;
                                            goal_ty = uu____1452;
                                            opts = (uu___95_1450.opts)
                                          } in
                                        replace_cur uu____1449 in
                                      bind uu____1447
                                        (fun uu____1460  ->
                                           let uu____1461 =
                                             let uu____1466 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 bv in
                                             (uu____1466, b1) in
                                           ret uu____1461)
                                    else fail "intro_rec: unification failed"))))))
        | FStar_Pervasives_Native.None  ->
            let uu____1480 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1480))
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
           let uu____1507 =
             let uu____1509 = FStar_List.map tr s in
             FStar_List.flatten uu____1509 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1507 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___96_1517 = goal in
            {
              context = (uu___96_1517.context);
              witness = w;
              goal_ty = t;
              opts = (uu___96_1517.opts)
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
       let uu____1534 = istrivial goal.context goal.goal_ty in
       if uu____1534
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____1538 = FStar_Syntax_Print.term_to_string goal.goal_ty in
          fail1 "Not a trivial goal: %s" uu____1538))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1548 =
           try
             let uu____1564 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
             ret uu____1564
           with
           | e ->
               let uu____1581 = FStar_Syntax_Print.term_to_string t in
               let uu____1582 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact: term is not typeable: %s (%s)" uu____1581
                 uu____1582 in
         bind uu____1548
           (fun uu____1594  ->
              match uu____1594 with
              | (t1,typ,guard) ->
                  let uu____1602 =
                    let uu____1603 =
                      let uu____1604 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1604 in
                    Prims.op_Negation uu____1603 in
                  if uu____1602
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1607 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty in
                     if uu____1607
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1611 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____1612 =
                          let uu____1613 = bnorm goal.context typ in
                          FStar_Syntax_Print.term_to_string uu____1613 in
                        let uu____1614 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1611 uu____1612 uu____1614))))
let exact_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1624 =
           try
             let uu____1640 = FStar_TypeChecker_TcTerm.tc_term goal.context t in
             ret uu____1640
           with
           | e ->
               let uu____1657 = FStar_Syntax_Print.term_to_string t in
               let uu____1658 = FStar_Syntax_Print.tag_of_term t in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1657
                 uu____1658 in
         bind uu____1624
           (fun uu____1670  ->
              match uu____1670 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp () in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1682 =
                       let uu____1683 =
                         FStar_TypeChecker_Rel.is_trivial guard in
                       Prims.op_Negation uu____1683 in
                     if uu____1682
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1686 =
                          let uu____1691 =
                            let uu____1696 =
                              FStar_Syntax_Util.comp_to_comp_typ comp in
                            uu____1696.FStar_Syntax_Syntax.effect_args in
                          match uu____1691 with
                          | pre::post::uu____1703 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____1724 ->
                              failwith "exact_lemma: impossible: not a lemma" in
                        match uu____1686 with
                        | (pre,post) ->
                            let uu____1740 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty in
                            if uu____1740
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1744  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____1746 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____1747 =
                                 FStar_Syntax_Print.term_to_string post in
                               let uu____1748 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1746 uu____1747 uu____1748)))))
let uvar_free_in_goal: FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1759 =
          let uu____1763 = FStar_Syntax_Free.uvars g.goal_ty in
          FStar_Util.set_elements uu____1763 in
        FStar_List.map FStar_Pervasives_Native.fst uu____1759 in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
let uvar_free: FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals
let rec __apply: Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1792 = let uu____1795 = exact tm in trytac uu____1795 in
           bind uu____1792
             (fun r  ->
                match r with
                | FStar_Pervasives_Native.Some r1 -> ret ()
                | FStar_Pervasives_Native.None  ->
                    let uu____1804 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm in
                    (match uu____1804 with
                     | (tm1,typ,guard) ->
                         let uu____1812 =
                           let uu____1813 =
                             let uu____1814 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1814 in
                           Prims.op_Negation uu____1813 in
                         if uu____1812
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1817 = FStar_Syntax_Util.arrow_one typ in
                            match uu____1817 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____1824 =
                                  FStar_Syntax_Print.term_to_string typ in
                                fail1 "apply: cannot unify (%s)" uu____1824
                            | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                let uu____1834 =
                                  let uu____1835 =
                                    FStar_Syntax_Util.is_total_comp c in
                                  Prims.op_Negation uu____1835 in
                                if uu____1834
                                then fail "apply: not total"
                                else
                                  (let uu____1838 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort in
                                   bind uu____1838
                                     (fun uu____1849  ->
                                        match uu____1849 with
                                        | (u,g_u) ->
                                            let tm' =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                tm1 [(u, aq)]
                                                FStar_Pervasives_Native.None
                                                (goal.context).FStar_TypeChecker_Env.range in
                                            let uu____1863 = __apply uopt tm' in
                                            bind uu____1863
                                              (fun uu____1869  ->
                                                 let uu____1870 =
                                                   let uu____1871 =
                                                     let uu____1873 =
                                                       let uu____1874 =
                                                         FStar_Syntax_Util.head_and_args
                                                           u in
                                                       FStar_Pervasives_Native.fst
                                                         uu____1874 in
                                                     FStar_Syntax_Subst.compress
                                                       uu____1873 in
                                                   uu____1871.FStar_Syntax_Syntax.n in
                                                 match uu____1870 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     (uvar,uu____1889) ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1905 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps) in
                                                          if uu____1905
                                                          then ret ()
                                                          else
                                                            (let uu____1908 =
                                                               let uu____1910
                                                                 =
                                                                 let uu____1911
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u in
                                                                 let uu____1912
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1911;
                                                                   goal_ty =
                                                                    uu____1912;
                                                                   opts =
                                                                    (goal.opts)
                                                                 } in
                                                               [uu____1910] in
                                                             add_goals
                                                               uu____1908))
                                                 | uu____1913 -> ret ())))))))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1920 = __apply true tm in focus uu____1920
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1935 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1935 with
         | (tm1,t,guard) ->
             let uu____1943 =
               let uu____1944 =
                 let uu____1945 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1945 in
               Prims.op_Negation uu____1944 in
             if uu____1943
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1948 = FStar_Syntax_Util.arrow_formals_comp t in
                match uu____1948 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____1965 =
                         FStar_List.fold_left
                           (fun uu____1995  ->
                              fun uu____1996  ->
                                match (uu____1995, uu____1996) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort in
                                    let uu____2045 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t in
                                    (match uu____2045 with
                                     | (u,uu____2060,g_u) ->
                                         let uu____2068 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u in
                                         (((u, aq) :: uvs), uu____2068,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs in
                       match uu____1965 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____2100 =
                             let uu____2105 =
                               let uu____2110 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1 in
                               uu____2110.FStar_Syntax_Syntax.effect_args in
                             match uu____2105 with
                             | pre::post::uu____2117 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____2138 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma" in
                           (match uu____2100 with
                            | (pre,post) ->
                                let uu____2154 =
                                  let uu____2156 =
                                    FStar_Syntax_Util.mk_squash post in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____2156 goal.goal_ty in
                                (match uu____2154 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____2158 =
                                       let uu____2159 =
                                         FStar_Syntax_Util.mk_squash post in
                                       FStar_Syntax_Print.term_to_string
                                         uu____2159 in
                                     let uu____2160 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____2158 uu____2160
                                 | FStar_Pervasives_Native.Some g ->
                                     let uu____2162 =
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
                                            (fun uu____2207  ->
                                               match uu____2207 with
                                               | (uu____2214,uu____2215,uu____2216,tm2,uu____2218,uu____2219)
                                                   ->
                                                   let uu____2220 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____2220 with
                                                    | (hd1,uu____2229) ->
                                                        let uu____2240 =
                                                          let uu____2241 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____2241.FStar_Syntax_Syntax.n in
                                                        (match uu____2240
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____2243 ->
                                                             true
                                                         | uu____2252 ->
                                                             false)))) in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____2262  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____2272 =
                                                 let uu____2276 =
                                                   FStar_Syntax_Free.uvars t1 in
                                                 FStar_Util.set_elements
                                                   uu____2276 in
                                               FStar_List.map
                                                 FStar_Pervasives_Native.fst
                                                 uu____2272 in
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
                                             let uu____2306 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1 in
                                             match uu____2306 with
                                             | (hd1,uu____2315) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____2327) ->
                                                      appears uv goals
                                                  | uu____2340 -> false) in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____2366  ->
                                                     match uu____2366 with
                                                     | (_msg,_env,_uvar,term,typ,uu____2378)
                                                         ->
                                                         let uu____2379 =
                                                           bnorm goal.context
                                                             term in
                                                         let uu____2380 =
                                                           bnorm goal.context
                                                             typ in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____2379;
                                                           goal_ty =
                                                             uu____2380;
                                                           opts = (goal.opts)
                                                         })) in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____2412 = f x xs1 in
                                                 if uu____2412
                                                 then
                                                   let uu____2414 =
                                                     filter' f xs1 in
                                                   x :: uu____2414
                                                 else filter' f xs1 in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____2425 =
                                                      checkone g1.witness
                                                        goals in
                                                    Prims.op_Negation
                                                      uu____2425) sub_goals in
                                           let uu____2426 =
                                             add_irrelevant_goal goal.context
                                               pre goal.opts in
                                           bind uu____2426
                                             (fun uu____2430  ->
                                                let uu____2431 =
                                                  trytac trivial in
                                                bind uu____2431
                                                  (fun uu____2437  ->
                                                     let uu____2439 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits in
                                                     bind uu____2439
                                                       (fun uu____2442  ->
                                                          add_goals
                                                            sub_goals1))))))))))
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2452 =
           FStar_All.pipe_left mlog
             (fun uu____2460  ->
                let uu____2461 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____2462 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2461
                  uu____2462) in
         bind uu____2452
           (fun uu____2474  ->
              let uu____2475 =
                let uu____2477 =
                  let uu____2478 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____2478 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2477 in
              match uu____2475 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2485::(x,uu____2487)::(e,uu____2489)::[])) when
                  FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
                  let uu____2513 =
                    let uu____2514 = FStar_Syntax_Subst.compress x in
                    uu____2514.FStar_Syntax_Syntax.n in
                  (match uu____2513 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___101_2519 = goal in
                         let uu____2520 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness in
                         let uu____2522 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___101_2519.context);
                           witness = uu____2520;
                           goal_ty = uu____2522;
                           opts = (uu___101_2519.opts)
                         } in
                       replace_cur goal1
                   | uu____2524 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2525 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2531 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2531 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let uu____2544 = FStar_Util.set_mem x fns_ty in
           if uu____2544
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2547 = new_uvar env' goal.goal_ty in
              bind uu____2547
                (fun uu____2557  ->
                   match uu____2557 with
                   | (u,g) ->
                       let uu____2563 =
                         let uu____2564 =
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness u in
                         Prims.op_Negation uu____2564 in
                       if uu____2563
                       then fail "clear: unification failed"
                       else
                         (let new_goal =
                            let uu___102_2568 = goal in
                            let uu____2569 = bnorm env' u in
                            {
                              context = env';
                              witness = uu____2569;
                              goal_ty = (uu___102_2568.goal_ty);
                              opts = (uu___102_2568.opts)
                            } in
                          bind dismiss
                            (fun uu____2571  -> add_goals [new_goal])))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2581 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2581 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2598 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2598 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____2611 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____2611 in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None in
           replace_cur
             (let uu___103_2630 = goal in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___103_2630.opts)
              }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2640 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2640 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2652 = FStar_Syntax_Print.bv_to_string x in
               let uu____2653 = FStar_Syntax_Print.bv_to_string y in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2652 uu____2653
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2666 = revert_all_hd xs1 in
        bind uu____2666 (fun uu____2669  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___104_2684 = g in
           {
             context = ctx';
             witness = (uu___104_2684.witness);
             goal_ty = (uu___104_2684.goal_ty);
             opts = (uu___104_2684.opts)
           } in
         bind dismiss (fun uu____2686  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___105_2701 = g in
           {
             context = ctx';
             witness = (uu___105_2701.witness);
             goal_ty = (uu___105_2701.goal_ty);
             opts = (uu___105_2701.opts)
           } in
         bind dismiss (fun uu____2703  -> add_goals [g']))
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2737 = f x in
      bind uu____2737
        (fun y  ->
           let uu____2743 = mapM f xs in
           bind uu____2743 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2779 = FStar_Syntax_Subst.compress t in
          uu____2779.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2800 = ff hd1 in
              bind uu____2800
                (fun hd2  ->
                   let fa uu____2814 =
                     match uu____2814 with
                     | (a,q) ->
                         let uu____2822 = ff a in
                         bind uu____2822 (fun a1  -> ret (a1, q)) in
                   let uu____2830 = mapM fa args in
                   bind uu____2830
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2863 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2863 with
               | (bs1,t') ->
                   let uu____2869 =
                     let uu____2871 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2871 t' in
                   bind uu____2869
                     (fun t''  ->
                        let uu____2875 =
                          let uu____2876 =
                            let uu____2885 =
                              FStar_Syntax_Subst.close_binders bs1 in
                            let uu____2886 = FStar_Syntax_Subst.close bs1 t'' in
                            (uu____2885, uu____2886, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2876 in
                        ret uu____2875))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2898 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___106_2902 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___106_2902.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___106_2902.FStar_Syntax_Syntax.vars)
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
            let uu____2929 = FStar_TypeChecker_TcTerm.tc_term env t in
            match uu____2929 with
            | (t1,lcomp,g) ->
                let uu____2937 =
                  (let uu____2940 = FStar_Syntax_Util.is_total_lcomp lcomp in
                   Prims.op_Negation uu____2940) ||
                    (let uu____2942 = FStar_TypeChecker_Rel.is_trivial g in
                     Prims.op_Negation uu____2942) in
                if uu____2937
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                   let uu____2947 = new_uvar env typ in
                   bind uu____2947
                     (fun uu____2958  ->
                        match uu____2958 with
                        | (ut,guard) ->
                            (log ps
                               (fun uu____2968  ->
                                  let uu____2969 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  let uu____2970 =
                                    FStar_Syntax_Print.term_to_string ut in
                                  FStar_Util.print2
                                    "Pointwise_rec: making equality %s = %s\n"
                                    uu____2969 uu____2970);
                             (let uu____2971 =
                                let uu____2973 =
                                  let uu____2974 =
                                    FStar_TypeChecker_TcTerm.universe_of env
                                      typ in
                                  FStar_Syntax_Util.mk_eq2 uu____2974 typ t1
                                    ut in
                                add_irrelevant_goal env uu____2973 opts in
                              bind uu____2971
                                (fun uu____2977  ->
                                   let uu____2978 =
                                     bind tau
                                       (fun uu____2983  ->
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env guard;
                                          (let ut1 =
                                             FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                               env ut in
                                           ret ut1)) in
                                   focus uu____2978)))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____3001 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____3001 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____3024  ->
                   let uu____3025 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____3025);
              bind dismiss_all
                (fun uu____3028  ->
                   let uu____3029 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1 in
                   bind uu____3029
                     (fun gt'  ->
                        log ps
                          (fun uu____3038  ->
                             let uu____3039 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____3039);
                        (let uu____3040 = push_goals gs in
                         bind uu____3040
                           (fun uu____3043  ->
                              add_goals
                                [(let uu___107_3045 = g in
                                  {
                                    context = (uu___107_3045.context);
                                    witness = (uu___107_3045.witness);
                                    goal_ty = gt';
                                    opts = (uu___107_3045.opts)
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____3064 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____3064 with
       | FStar_Pervasives_Native.Some t ->
           let uu____3071 = FStar_Syntax_Util.head_and_args' t in
           (match uu____3071 with
            | (hd1,args) ->
                let uu____3089 =
                  let uu____3096 =
                    let uu____3097 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____3097.FStar_Syntax_Syntax.n in
                  (uu____3096, args) in
                (match uu____3089 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3105::(l,uu____3107)::(r,uu____3109)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____3133 =
                       let uu____3134 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____3134 in
                     if uu____3133
                     then
                       let uu____3136 = FStar_Syntax_Print.term_to_string l in
                       let uu____3137 = FStar_Syntax_Print.term_to_string r in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____3136 uu____3137
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____3141) ->
                     let uu____3150 = FStar_Syntax_Print.term_to_string t in
                     fail1 "trefl: not an equality (%s)" uu____3150))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
let dup: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____3156 = new_uvar g.context g.goal_ty in
       bind uu____3156
         (fun uu____3166  ->
            match uu____3166 with
            | (u,u_g) ->
                let g' =
                  let uu___108_3173 = g in
                  {
                    context = (uu___108_3173.context);
                    witness = u;
                    goal_ty = (uu___108_3173.goal_ty);
                    opts = (uu___108_3173.opts)
                  } in
                bind dismiss
                  (fun uu____3176  ->
                     let uu____3177 =
                       let uu____3179 =
                         let uu____3180 =
                           FStar_TypeChecker_TcTerm.universe_of g.context
                             g.goal_ty in
                         FStar_Syntax_Util.mk_eq2 uu____3180 g.goal_ty u
                           g.witness in
                       add_irrelevant_goal g.context uu____3179 g.opts in
                     bind uu____3177
                       (fun uu____3183  ->
                          let uu____3184 = add_goals [g'] in
                          bind uu____3184 (fun uu____3187  -> ret ())))))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___109_3201 = ps in
              {
                main_context = (uu___109_3201.main_context);
                main_goal = (uu___109_3201.main_goal);
                all_implicits = (uu___109_3201.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___109_3201.smt_goals)
              })
       | uu____3202 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___110_3213 = ps in
              {
                main_context = (uu___110_3213.main_context);
                main_goal = (uu___110_3213.main_goal);
                all_implicits = (uu___110_3213.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___110_3213.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____3218 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____3251 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____3251 with
         | (t1,typ,guard) ->
             let uu____3261 = FStar_Syntax_Util.head_and_args typ in
             (match uu____3261 with
              | (hd1,args) ->
                  let uu____3284 =
                    let uu____3291 =
                      let uu____3292 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____3292.FStar_Syntax_Syntax.n in
                    (uu____3291, args) in
                  (match uu____3284 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____3303)::(q,uu____3305)::[]) when
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
                         let uu___111_3326 = g in
                         let uu____3327 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____3327;
                           witness = (uu___111_3326.witness);
                           goal_ty = (uu___111_3326.goal_ty);
                           opts = (uu___111_3326.opts)
                         } in
                       let g2 =
                         let uu___112_3329 = g in
                         let uu____3330 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____3330;
                           witness = (uu___112_3329.witness);
                           goal_ty = (uu___112_3329.goal_ty);
                           opts = (uu___112_3329.opts)
                         } in
                       bind dismiss
                         (fun uu____3335  ->
                            let uu____3336 = add_goals [g1; g2] in
                            bind uu____3336
                              (fun uu____3342  ->
                                 let uu____3343 =
                                   let uu____3346 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____3347 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____3346, uu____3347) in
                                 ret uu____3343))
                   | uu____3350 ->
                       let uu____3357 = FStar_Syntax_Print.term_to_string typ in
                       fail1 "Not a disjunction: %s" uu____3357)))
let set_options: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____3376 = FStar_Util.smap_copy g.opts in
          FStar_Options.set uu____3376);
         (let res = FStar_Options.set_options FStar_Options.Set s in
          let opts' = FStar_Options.peek () in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___113_3382 = g in
                 {
                   context = (uu___113_3382.context);
                   witness = (uu___113_3382.witness);
                   goal_ty = (uu___113_3382.goal_ty);
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
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (proofstate,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____3408 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ in
      match uu____3408 with
      | (u,uu____3418,g_u) ->
          let g =
            let uu____3427 = FStar_Options.peek () in
            { context = env; witness = u; goal_ty = typ; opts = uu____3427 } in
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            } in
          (ps, u)