open Prims
type name = FStar_Syntax_Syntax.bv
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
type goal =
  {
  context: FStar_TypeChecker_Env.env;
  witness: FStar_Syntax_Syntax.term option;
  goal_ty: FStar_Syntax_Syntax.term;}
type proofstate =
  {
  main_context: FStar_TypeChecker_Env.env;
  main_goal: goal;
  all_implicits: FStar_TypeChecker_Env.implicits;
  goals: goal Prims.list;
  smt_goals: goal Prims.list;
  transaction: FStar_Syntax_Unionfind.tx;}
type 'a result =
  | Success of ('a* proofstate)
  | Failed of (Prims.string* proofstate)
let uu___is_Success projectee =
  match projectee with | Success _0 -> true | uu____114 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success _0 -> _0
let uu___is_Failed projectee =
  match projectee with | Failed _0 -> true | uu____145 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed _0 -> _0
exception Failure of Prims.string
let uu___is_Failure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Failure uu____170 -> true | uu____171 -> false
let __proj__Failure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Failure uu____178 -> uu____178
type 'a tac = {
  tac_f: proofstate -> 'a result;}
let mk_tac f = { tac_f = f }
let run t p = t.tac_f p
let ret x = mk_tac (fun p  -> Success (x, p))
let bind t1 t2 =
  mk_tac
    (fun p  ->
       let uu____279 = run t1 p in
       match uu____279 with
       | Success (a,q) -> let uu____284 = t2 a in run uu____284 q
       | Failed (msg,q) -> Failed (msg, q))
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____292 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____292
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____293 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format2 "%s |- %s" g_binders uu____293
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____303 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____303
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____313 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____313
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____326 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____326
let dump_goal ps goal =
  let uu____340 = goal_to_string goal in tacprint uu____340
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint1 "State dump (%s):" msg;
      (let uu____349 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____349);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____355 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____355);
      FStar_List.iter (dump_goal ps) ps.smt_goals
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let log ps f =
  let uu____389 = FStar_ST.read tacdbg in if uu____389 then f () else ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg = mk_tac (fun p  -> Failed (msg, p))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____423  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      match goal.witness with
      | None  -> ()
      | Some w ->
          let uu____431 =
            FStar_TypeChecker_Rel.teq_nosmt goal.context w solution in
          if uu____431
          then ()
          else
            (let uu____433 =
               let uu____434 =
                 let uu____435 = FStar_Syntax_Print.term_to_string solution in
                 let uu____436 = FStar_Syntax_Print.term_to_string w in
                 let uu____437 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 FStar_Util.format3 "%s does not solve %s : %s" uu____435
                   uu____436 uu____437 in
               Failure uu____434 in
             raise uu____433)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____442 =
         let uu___79_443 = p in
         let uu____444 = FStar_List.tl p.goals in
         {
           main_context = (uu___79_443.main_context);
           main_goal = (uu___79_443.main_goal);
           all_implicits = (uu___79_443.all_implicits);
           goals = uu____444;
           smt_goals = (uu___79_443.smt_goals);
           transaction = (uu___79_443.transaction)
         } in
       set uu____442)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___80_451 = p in
          {
            main_context = (uu___80_451.main_context);
            main_goal = (uu___80_451.main_goal);
            all_implicits = (uu___80_451.all_implicits);
            goals = [];
            smt_goals = (uu___80_451.smt_goals);
            transaction = (uu___80_451.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_463 = p in
            {
              main_context = (uu___81_463.main_context);
              main_goal = (uu___81_463.main_goal);
              all_implicits = (uu___81_463.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___81_463.smt_goals);
              transaction = (uu___81_463.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_475 = p in
            {
              main_context = (uu___82_475.main_context);
              main_goal = (uu___82_475.main_goal);
              all_implicits = (uu___82_475.all_implicits);
              goals = (uu___82_475.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___82_475.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____482  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___83_492 = p in
            {
              main_context = (uu___83_492.main_context);
              main_goal = (uu___83_492.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___83_492.goals);
              smt_goals = (uu___83_492.smt_goals);
              transaction = (uu___83_492.transaction)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____502 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____502 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid
    | uu____514 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____519 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____519 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid
    | uu____531 -> false
let conj_goals: goal -> goal -> goal =
  fun g1  ->
    fun g2  ->
      let t1 = g1.goal_ty in
      let t2 = g2.goal_ty in
      let uu____541 = (is_true t1) || (is_false t2) in
      if uu____541
      then g2
      else
        (let uu____543 = (is_true t2) || (is_false t1) in
         if uu____543
         then g1
         else
           (let uu___84_545 = g1 in
            let uu____546 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___84_545.context);
              witness = (uu___84_545.witness);
              goal_ty = uu____546
            }))
let with_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with | [] -> fail "No more goals" | hd1::tl1 -> f hd1)
let cur_goal: goal tac =
  mk_tac
    (fun ps  ->
       match ps.goals with
       | hd1::uu____580 -> Success (hd1, ps)
       | uu____582 -> Failed ("No goals left", ps))
let set_cur_goal: goal -> Prims.unit tac =
  fun g  ->
    mk_tac
      (fun ps  ->
         match ps.goals with
         | hd1::tl1 ->
             Success
               ((),
                 (let uu___85_598 = ps in
                  {
                    main_context = (uu___85_598.main_context);
                    main_goal = (uu___85_598.main_goal);
                    all_implicits = (uu___85_598.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___85_598.smt_goals);
                    transaction = (uu___85_598.transaction)
                  }))
         | uu____599 -> Failed ("No goals left", ps))
let replace_point:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun e1  ->
    fun e2  ->
      fun t  ->
        let uu____610 = FStar_Syntax_Util.term_eq e1 t in
        if uu____610 then e2 else t
let treplace env e1 e2 t =
  FStar_Syntax_Util.bottom_fold (replace_point e1 e2) t
let grewrite_impl:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.unit tac
  =
  fun t1  ->
    fun t2  ->
      fun e1  ->
        fun e2  ->
          bind cur_goal
            (fun g  ->
               let env = g.context in
               let ok =
                 let uu____656 = FStar_TypeChecker_Rel.try_teq true env t1 t2 in
                 match uu____656 with
                 | None  -> false
                 | Some g1 -> FStar_TypeChecker_Rel.is_trivial g1 in
               if ok
               then
                 let goal_ty' = treplace env e1 e2 g.goal_ty in
                 let uu____661 =
                   set_cur_goal
                     (let uu___86_665 = g in
                      {
                        context = (uu___86_665.context);
                        witness = (uu___86_665.witness);
                        goal_ty = goal_ty'
                      }) in
                 bind uu____661
                   (fun uu____668  ->
                      let uu____669 =
                        let uu____671 =
                          let uu____672 =
                            FStar_Syntax_Util.mk_eq2
                              FStar_Syntax_Syntax.U_zero t1 e1 e2 in
                          {
                            context = (g.context);
                            witness = None;
                            goal_ty = uu____672
                          } in
                        [uu____671] in
                      add_goals uu____669)
               else
                 (FStar_TypeChecker_Err.add_errors env
                    [("Ill-type rewriting requested",
                       (e1.FStar_Syntax_Syntax.pos))];
                  fail "grewrite: Ill-typed rewriting requested"))
let smt: Prims.unit tac =
  with_cur_goal "smt"
    (fun g  ->
       bind dismiss
         (fun uu____684  ->
            let uu____685 =
              add_goals
                [(let uu___87_688 = g in
                  {
                    context = (uu___87_688.context);
                    witness = (uu___87_688.witness);
                    goal_ty = FStar_Syntax_Util.t_true
                  })] in
            bind uu____685 (fun uu____690  -> add_smt_goals [g])))
let focus_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___88_713 = p in
             {
               main_context = (uu___88_713.main_context);
               main_goal = (uu___88_713.main_goal);
               all_implicits = (uu___88_713.all_implicits);
               goals = [hd1];
               smt_goals = (uu___88_713.smt_goals);
               transaction = (uu___88_713.transaction)
             } in
           let uu____714 = set q in
           bind uu____714
             (fun uu____717  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___89_725 = q' in
                            {
                              main_context = (uu___89_725.main_context);
                              main_goal = (uu___89_725.main_goal);
                              all_implicits = (uu___89_725.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___89_725.smt_goals);
                              transaction = (uu___89_725.transaction)
                            } in
                          let uu____726 = set q2 in
                          bind uu____726 (fun uu____729  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | uu____764::[] -> bind f (fun a  -> ret (a, None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____782  ->
                let uu____783 = add_goals [hd1] in
                bind uu____783
                  (fun uu____789  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____805  ->
                               match uu____805 with
                               | { main_context = uu____810;
                                   main_goal = uu____811;
                                   all_implicits = uu____812;
                                   goals = sub_goals_f;
                                   smt_goals = uu____814;
                                   transaction = uu____815;_} ->
                                   bind dismiss_all
                                     (fun uu____823  ->
                                        let uu____824 = add_goals tl1 in
                                        bind uu____824
                                          (fun uu____830  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____837 =
                                                    add_goals sub_goals_f in
                                                  bind uu____837
                                                    (fun uu____843  ->
                                                       ret (a, (Some b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____869 = t1.tac_f p in
       match uu____869 with | Failed uu____872 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____892 =
         let uu____895 =
           let uu____901 = map t in cur_goal_and_rest t uu____901 in
         bind uu____895
           (fun uu___78_912  ->
              match uu___78_912 with
              | (hd1,None ) -> ret [hd1]
              | (hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____892 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal "map_goal"
        (fun g  ->
           let uu____947 =
             let uu___90_948 = g in
             let uu____949 = f g.goal_ty in
             {
               context = (uu___90_948.context);
               witness = (uu___90_948.witness);
               goal_ty = uu____949
             } in
           replace_cur uu____947) in
    let uu____950 = map aux in bind uu____950 (fun uu____955  -> ret ())
let map_meta t =
  with_cur_goal "map_meta"
    (fun g  ->
       let uu____973 =
         let uu____974 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____974.FStar_Syntax_Syntax.n in
       match uu____973 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____984 =
             replace_cur
               (let uu___91_988 = g in
                {
                  context = (uu___91_988.context);
                  witness = (uu___91_988.witness);
                  goal_ty = f
                }) in
           bind uu____984
             (fun uu____990  ->
                bind t
                  (fun a  ->
                     let uu____994 =
                       map_goal_term
                         (fun tm  ->
                            let uu____1001 = is_true tm in
                            if uu____1001
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____994 (fun uu____1008  -> ret a)))
       | uu____1009 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1022 =
        bind t1
          (fun uu____1026  ->
             let uu____1027 = map t2 in
             bind uu____1027 (fun uu____1032  -> ret ())) in
      focus_cur_goal "seq" uu____1022
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal "intros"
    (fun goal  ->
       let uu____1043 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1043 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____1053  ->
                let uu____1054 = add_goals [new_goal] in
                bind uu____1054
                  (fun uu____1058  ->
                     let uu____1059 =
                       FStar_All.pipe_left mlog
                         (fun uu____1066  ->
                            let uu____1067 =
                              FStar_Syntax_Print.binders_to_string ", " bs in
                            FStar_Util.print1 "intros: %s\n" uu____1067) in
                     bind uu____1059 (fun uu____1069  -> ret bs)))
       | uu____1070 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____1074  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____1085 =
    let uu____1091 = FStar_Syntax_Syntax.as_arg p in [uu____1091] in
  FStar_Syntax_Util.mk_app sq uu____1085
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option
  =
  fun t  ->
    let uu____1098 = FStar_Syntax_Util.head_and_args t in
    match uu____1098 with
    | (head1,args) ->
        let uu____1127 =
          let uu____1135 =
            let uu____1136 = FStar_Syntax_Util.un_uinst head1 in
            uu____1136.FStar_Syntax_Syntax.n in
          (uu____1135, args) in
        (match uu____1127 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____1149)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1169;
               FStar_Syntax_Syntax.index = uu____1170;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1172;
                   FStar_Syntax_Syntax.pos = uu____1173;
                   FStar_Syntax_Syntax.vars = uu____1174;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____1193 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal "imp_intro"
    (fun goal  ->
       let uu____1214 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1214 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1219)::(rhs,uu____1221)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1249 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1249; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1252  ->
                let uu____1253 = add_goals [new_goal] in
                bind uu____1253
                  (fun uu____1257  ->
                     let uu____1258 =
                       FStar_All.pipe_left mlog
                         (fun uu____1265  ->
                            let uu____1266 =
                              FStar_Syntax_Print.bv_to_string name in
                            FStar_Util.print1 "imp_intro: %s\n" uu____1266) in
                     bind uu____1258
                       (fun uu____1269  ->
                          let uu____1270 = FStar_Syntax_Syntax.mk_binder name in
                          ret uu____1270)))
       | uu____1271 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal "split"
    (fun goal  ->
       let uu____1280 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1280 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1294  ->
                     match uu____1294 with
                     | (a,uu____1298) ->
                         let uu___92_1299 = goal in
                         {
                           context = (uu___92_1299.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1301  -> add_goals new_goals)
       | uu____1302 -> fail "Cannot split this goal; expected a conjunction")
let trivial: Prims.unit tac =
  with_cur_goal "trivial"
    (fun goal  ->
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.Beta;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Zeta;
         FStar_TypeChecker_Normalize.Iota;
         FStar_TypeChecker_Normalize.Primops] in
       let t =
         FStar_TypeChecker_Normalize.normalize steps goal.context
           goal.goal_ty in
       let uu____1314 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1314 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid ->
           bind dismiss
             (fun uu____1328  ->
                add_goals
                  [(let uu___93_1330 = goal in
                    {
                      context = (uu___93_1330.context);
                      witness = (uu___93_1330.witness);
                      goal_ty = t
                    })])
       | uu____1331 -> fail "Not a trivial goal")
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "apply_lemma"
      (fun goal  ->
         try
           let uu____1349 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1349 with
           | (tm1,t,guard) ->
               let uu____1357 =
                 let uu____1358 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1358 in
               if uu____1357
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1361 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1361 with
                  | (bs,comp) ->
                      let uu____1376 =
                        FStar_List.fold_left
                          (fun uu____1406  ->
                             fun uu____1407  ->
                               match (uu____1406, uu____1407) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1456 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1456 with
                                    | (u,uu____1471,g_u) ->
                                        let uu____1479 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1479,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1376 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1511 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1527 ->
                                 ((fst pre), (fst post))
                             | uu____1557 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1511 with
                            | (pre,post) ->
                                let uu____1580 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1580 with
                                 | None  ->
                                     fail
                                       "apply_lemma: does not unify with goal"
                                 | Some g ->
                                     let g1 =
                                       let uu____1585 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1585
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1631  ->
                                               match uu____1631 with
                                               | (uu____1638,uu____1639,uu____1640,tm2,uu____1642,uu____1643)
                                                   ->
                                                   let uu____1644 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1644 with
                                                    | (hd1,uu____1655) ->
                                                        let uu____1670 =
                                                          let uu____1671 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1671.FStar_Syntax_Syntax.n in
                                                        (match uu____1670
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1674 ->
                                                             true
                                                         | uu____1685 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____1689 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____1712  ->
                                                   match uu____1712 with
                                                   | (_msg,_env,_uvar,term,typ,uu____1724)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (Some term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___96_1726 = goal in
                                          {
                                            context = (uu___96_1726.context);
                                            witness = None;
                                            goal_ty = pre
                                          }) :: uu____1689 in
                                       let uu____1727 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1727
                                         (fun uu____1730  ->
                                            bind dismiss
                                              (fun uu____1732  ->
                                                 add_goals sub_goals))))))))
         with | uu____1737 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "exact"
      (fun goal  ->
         try
           let uu____1755 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1755 with
           | (uu____1760,t,guard) ->
               let uu____1763 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1763
               then
                 (solve goal tm;
                  replace_cur
                    (let uu___99_1768 = goal in
                     {
                       context = (uu___99_1768.context);
                       witness = None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____1771 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1772 = FStar_Syntax_Print.term_to_string t in
                    let uu____1773 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1771
                      uu____1772 uu____1773 in
                  fail msg)
         with
         | e ->
             let uu____1780 =
               let uu____1781 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1781 in
             fail uu____1780)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal "rewrite"
      (fun goal  ->
         let uu____1790 =
           FStar_All.pipe_left mlog
             (fun uu____1798  ->
                let uu____1799 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____1800 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1799
                  uu____1800) in
         bind uu____1790
           (fun uu____1812  ->
              let uu____1813 =
                let uu____1815 =
                  let uu____1816 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____1816 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1815 in
              match uu____1813 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1823::(x,uu____1825)::(e,uu____1827)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____1861 =
                    let uu____1862 = FStar_Syntax_Subst.compress x in
                    uu____1862.FStar_Syntax_Syntax.n in
                  (match uu____1861 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___100_1868 = goal in
                         let uu____1869 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___100_1868.context);
                           witness = (uu___100_1868.witness);
                           goal_ty = uu____1869
                         } in
                       replace_cur goal1
                   | uu____1872 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____1873 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal "clear"
    (fun goal  ->
       let uu____1879 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1879 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1892 = FStar_Util.set_mem x fns in
           if uu____1892
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___101_1896 = goal in
                {
                  context = env';
                  witness = (uu___101_1896.witness);
                  goal_ty = (uu___101_1896.goal_ty)
                } in
              bind dismiss (fun uu____1898  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "clear_hd"
      (fun goal  ->
         let uu____1907 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1907 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal "revert"
    (fun goal  ->
       let uu____1924 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1924 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1938 = FStar_Util.set_mem x fvs in
             if uu____1938
             then
               let uu___102_1939 = goal in
               let uu____1940 =
                 let uu____1941 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1941 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___102_1939.witness);
                 goal_ty = uu____1940
               }
             else
               (let uu___103_1943 = goal in
                let uu____1944 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___103_1943.witness);
                  goal_ty = uu____1944
                }) in
           bind dismiss (fun uu____1946  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "revert_hd"
      (fun goal  ->
         let uu____1955 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1955 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1967 =
                 let uu____1968 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1969 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1968 uu____1969 in
               fail uu____1967
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1981 = revert_all_hd xs1 in
        bind uu____1981 (fun uu____1984  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1988 =
      let uu____1989 = FStar_Syntax_Subst.compress x in
      uu____1989.FStar_Syntax_Syntax.n in
    match uu____1988 with
    | FStar_Syntax_Syntax.Tm_name uu____1992 -> true
    | uu____1993 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1997 =
      let uu____1998 = FStar_Syntax_Subst.compress x in
      uu____1998.FStar_Syntax_Syntax.n in
    match uu____1997 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____2002 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) option
  =
  fun t  ->
    let uu____2014 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____2014 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____2026)::(rhs,uu____2028)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____2054 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____2054 with
         | Some (FStar_Syntax_Util.BaseConn
             (eq1,uu____2065::(x,uu____2067)::(e,uu____2069)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____2103 =
               let uu____2111 = as_name x in (uu____2111, e, rhs) in
             Some uu____2103
         | Some (FStar_Syntax_Util.BaseConn
             (eq1,(x,uu____2125)::(e,uu____2127)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____2153 =
               let uu____2161 = as_name x in (uu____2161, e, rhs) in
             Some uu____2153
         | uu____2173 -> None)
    | uu____2182 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | [] -> ret a
            | uu____2206::[] -> ret a
            | uu____2207 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____2222 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____2222
           then
             let uu____2224 =
               let uu___104_2225 = p in
               let uu____2226 =
                 let uu____2228 = conj_goals g1 g2 in uu____2228 :: rest in
               {
                 main_context = (uu___104_2225.main_context);
                 main_goal = (uu___104_2225.main_goal);
                 all_implicits = (uu___104_2225.all_implicits);
                 goals = uu____2226;
                 smt_goals = (uu___104_2225.smt_goals);
                 transaction = (uu___104_2225.transaction)
               } in
             set uu____2224
           else
             (let g1_binders =
                let uu____2231 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____2231
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____2233 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____2233
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____2234 =
                let uu____2235 = goal_to_string g1 in
                let uu____2236 = goal_to_string g2 in
                let uu____2237 =
                  let uu____2238 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____2238 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____2235 uu____2236 uu____2237 in
              fail uu____2234)
       | uu____2239 ->
           let goals =
             let uu____2242 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____2242 (FStar_String.concat "\n\t") in
           let uu____2249 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____2249)
let rec visit: Prims.unit tac -> Prims.unit tac =
  fun callback  ->
    let uu____2257 =
      let uu____2259 =
        with_cur_goal "visit_strengthen_else"
          (fun goal  ->
             let uu____2267 =
               FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
             match uu____2267 with
             | None  ->
                 let uu____2270 =
                   let uu____2271 = FStar_Syntax_Subst.compress goal.goal_ty in
                   uu____2271.FStar_Syntax_Syntax.n in
                 (match uu____2270 with
                  | FStar_Syntax_Syntax.Tm_meta uu____2275 ->
                      let uu____2280 = visit callback in map_meta uu____2280
                  | uu____2282 ->
                      let uu____2283 =
                        FStar_All.pipe_left mlog
                          (fun uu____2290  ->
                             let uu____2291 =
                               FStar_Syntax_Print.term_to_string goal.goal_ty in
                             FStar_Util.print1
                               "Not a formula, split to smt %s\n" uu____2291) in
                      bind uu____2283 (fun uu____2293  -> smt))
             | Some (FStar_Syntax_Util.QEx uu____2294) ->
                 let uu____2298 =
                   FStar_All.pipe_left mlog
                     (fun uu____2305  ->
                        let uu____2306 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        FStar_Util.print1
                          "Not yet handled: exists\n\tGoal is %s\n"
                          uu____2306) in
                 bind uu____2298 (fun uu____2308  -> ret ())
             | Some (FStar_Syntax_Util.QAll (xs,uu____2310,uu____2311)) ->
                 bind intros
                   (fun binders  ->
                      let uu____2316 = visit callback in
                      let uu____2318 =
                        let uu____2320 =
                          let uu____2322 =
                            FStar_List.map FStar_Pervasives.fst binders in
                          revert_all_hd uu____2322 in
                        bind uu____2320
                          (fun uu____2327  ->
                             with_cur_goal "inner"
                               (fun goal1  ->
                                  let uu____2331 =
                                    FStar_All.pipe_left mlog
                                      (fun uu____2338  ->
                                         let uu____2339 =
                                           goal_to_string goal1 in
                                         FStar_Util.print1
                                           "After reverting intros, goal is %s\n"
                                           uu____2339) in
                                  bind uu____2331 (fun uu____2341  -> ret ()))) in
                      seq uu____2316 uu____2318)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2343)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
                 let uu____2344 =
                   let uu____2346 = visit callback in seq split uu____2346 in
                 bind uu____2344 (fun uu____2349  -> merge_sub_goals)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2351)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
                 bind imp_intro
                   (fun h  ->
                      let uu____2355 = visit callback in
                      seq uu____2355 revert)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2358)) ->
                 or_else trivial smt) in
      or_else callback uu____2259 in
    focus_cur_goal "visit_strengthen" uu____2257
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2362 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2366 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2370 -> false
let order_binder:
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder -> order =
  fun x  ->
    fun y  ->
      let n1 = FStar_Syntax_Syntax.order_bv (fst x) (fst y) in
      if n1 < (Prims.parse_int "0")
      then Lt
      else if n1 = (Prims.parse_int "0") then Eq else Gt
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> proofstate =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____2387 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2387 } in
      let uu____2388 = FStar_Syntax_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2388
      }