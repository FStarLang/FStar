open Prims
type name = FStar_Syntax_Syntax.bv
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
type goal =
  {
  context: FStar_TypeChecker_Env.env;
  witness: FStar_Syntax_Syntax.term FStar_Pervasives_Native.option;
  goal_ty: FStar_Syntax_Syntax.term;}
type proofstate =
  {
  main_context: FStar_TypeChecker_Env.env;
  main_goal: goal;
  all_implicits: FStar_TypeChecker_Env.implicits;
  goals: goal Prims.list;
  smt_goals: goal Prims.list;
  transaction: FStar_Unionfind.tx;}
type 'a result =
  | Success of ('a,proofstate) FStar_Pervasives_Native.tuple2
  | Failed of (Prims.string,proofstate) FStar_Pervasives_Native.tuple2
let uu___is_Success projectee =
  match projectee with | Success _0 -> true | uu____133 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success _0 -> _0
let uu___is_Failed projectee =
  match projectee with | Failed _0 -> true | uu____175 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed _0 -> _0
exception Failure of Prims.string
let uu___is_Failure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Failure uu____207 -> true | uu____208 -> false
let __proj__Failure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Failure uu____215 -> uu____215
type 'a tac = {
  tac_f: proofstate -> 'a result;}
let mk_tac f = { tac_f = f }
let run t p = t.tac_f p
let ret x = mk_tac (fun p  -> Success (x, p))
let bind t1 t2 =
  mk_tac
    (fun p  ->
       let uu____328 = run t1 p in
       match uu____328 with
       | Success (a,q) -> let uu____335 = t2 a in run uu____335 q
       | Failed (msg,q) -> Failed (msg, q))
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____344 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____344
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____345 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format2 "%s |- %s" g_binders uu____345
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____355 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____355
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____365 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____365
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____378 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____378
let dump_goal ps goal =
  let uu____392 = goal_to_string goal in tacprint uu____392
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint1 "State dump (%s):" msg;
      (let uu____401 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____401);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____404 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____404);
      FStar_List.iter (dump_goal ps) ps.smt_goals
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let log ps f =
  let uu____435 = FStar_ST.read tacdbg in if uu____435 then f () else ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg = mk_tac (fun p  -> Failed (msg, p))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____468  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      match goal.witness with
      | FStar_Pervasives_Native.None  -> ()
      | FStar_Pervasives_Native.Some w ->
          let uu____476 =
            FStar_TypeChecker_Rel.teq_nosmt goal.context w solution in
          if uu____476
          then ()
          else
            (let uu____478 =
               let uu____479 =
                 let uu____480 = FStar_Syntax_Print.term_to_string solution in
                 let uu____481 = FStar_Syntax_Print.term_to_string w in
                 let uu____482 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 FStar_Util.format3 "%s does not solve %s : %s" uu____480
                   uu____481 uu____482 in
               Failure uu____479 in
             raise uu____478)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____486 =
         let uu___79_487 = p in
         let uu____488 = FStar_List.tl p.goals in
         {
           main_context = (uu___79_487.main_context);
           main_goal = (uu___79_487.main_goal);
           all_implicits = (uu___79_487.all_implicits);
           goals = uu____488;
           smt_goals = (uu___79_487.smt_goals);
           transaction = (uu___79_487.transaction)
         } in
       set uu____486)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___80_494 = p in
          {
            main_context = (uu___80_494.main_context);
            main_goal = (uu___80_494.main_goal);
            all_implicits = (uu___80_494.all_implicits);
            goals = [];
            smt_goals = (uu___80_494.smt_goals);
            transaction = (uu___80_494.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_507 = p in
            {
              main_context = (uu___81_507.main_context);
              main_goal = (uu___81_507.main_goal);
              all_implicits = (uu___81_507.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___81_507.smt_goals);
              transaction = (uu___81_507.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_520 = p in
            {
              main_context = (uu___82_520.main_context);
              main_goal = (uu___82_520.main_goal);
              all_implicits = (uu___82_520.all_implicits);
              goals = (uu___82_520.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___82_520.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____528  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___83_537 = p in
            {
              main_context = (uu___83_537.main_context);
              main_goal = (uu___83_537.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___83_537.goals);
              smt_goals = (uu___83_537.smt_goals);
              transaction = (uu___83_537.transaction)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____553 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____553 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Parser_Const.true_lid
    | uu____575 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____581 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____581 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Parser_Const.false_lid
    | uu____603 -> false
let conj_goals: goal -> goal -> goal =
  fun g1  ->
    fun g2  ->
      let t1 = g1.goal_ty in
      let t2 = g2.goal_ty in
      let uu____614 = (is_true t1) || (is_false t2) in
      if uu____614
      then g2
      else
        (let uu____616 = (is_true t2) || (is_false t1) in
         if uu____616
         then g1
         else
           (let uu___84_618 = g1 in
            let uu____619 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___84_618.context);
              witness = (uu___84_618.witness);
              goal_ty = uu____619
            }))
let with_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with | [] -> fail "No more goals" | hd1::tl1 -> f hd1)
let cur_goal: goal tac =
  mk_tac
    (fun ps  ->
       match ps.goals with
       | hd1::uu____656 -> Success (hd1, ps)
       | uu____659 -> Failed ("No goals left", ps))
let set_cur_goal: goal -> Prims.unit tac =
  fun g  ->
    mk_tac
      (fun ps  ->
         match ps.goals with
         | hd1::tl1 ->
             Success
               ((),
                 (let uu___85_676 = ps in
                  {
                    main_context = (uu___85_676.main_context);
                    main_goal = (uu___85_676.main_goal);
                    all_implicits = (uu___85_676.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___85_676.smt_goals);
                    transaction = (uu___85_676.transaction)
                  }))
         | uu____677 -> Failed ("No goals left", ps))
let replace_point:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun e1  ->
    fun e2  ->
      fun t  ->
        let uu____689 = FStar_Syntax_Util.term_eq e1 t in
        if uu____689 then e2 else t
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
                 let uu____732 = FStar_TypeChecker_Rel.try_teq true env t1 t2 in
                 match uu____732 with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some g1 ->
                     FStar_TypeChecker_Rel.is_trivial g1 in
               if ok
               then
                 let goal_ty' = treplace env e1 e2 g.goal_ty in
                 let uu____739 =
                   set_cur_goal
                     (let uu___86_742 = g in
                      {
                        context = (uu___86_742.context);
                        witness = (uu___86_742.witness);
                        goal_ty = goal_ty'
                      }) in
                 bind uu____739
                   (fun uu____743  ->
                      let uu____744 =
                        let uu____747 =
                          let uu____748 =
                            FStar_Syntax_Util.mk_eq2
                              FStar_Syntax_Syntax.U_zero t1 e1 e2 in
                          {
                            context = (g.context);
                            witness = FStar_Pervasives_Native.None;
                            goal_ty = uu____748
                          } in
                        [uu____747] in
                      add_goals uu____744)
               else
                 (FStar_TypeChecker_Err.add_errors env
                    [("Ill-type rewriting requested",
                       (e1.FStar_Syntax_Syntax.pos))];
                  fail "grewrite: Ill-typed rewriting requested"))
let smt: Prims.unit tac =
  with_cur_goal "smt"
    (fun g  ->
       bind dismiss
         (fun uu____762  ->
            let uu____763 =
              add_goals
                [(let uu___87_766 = g in
                  {
                    context = (uu___87_766.context);
                    witness = (uu___87_766.witness);
                    goal_ty = FStar_Syntax_Util.t_true
                  })] in
            bind uu____763 (fun uu____767  -> add_smt_goals [g])))
let focus_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___88_794 = p in
             {
               main_context = (uu___88_794.main_context);
               main_goal = (uu___88_794.main_goal);
               all_implicits = (uu___88_794.all_implicits);
               goals = [hd1];
               smt_goals = (uu___88_794.smt_goals);
               transaction = (uu___88_794.transaction)
             } in
           let uu____795 = set q in
           bind uu____795
             (fun uu____798  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___89_802 = q' in
                            {
                              main_context = (uu___89_802.main_context);
                              main_goal = (uu___89_802.main_goal);
                              all_implicits = (uu___89_802.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___89_802.smt_goals);
                              transaction = (uu___89_802.transaction)
                            } in
                          let uu____803 = set q2 in
                          bind uu____803 (fun uu____806  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | uu____858::[] ->
           bind f (fun a  -> ret (a, FStar_Pervasives_Native.None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____884  ->
                let uu____885 = add_goals [hd1] in
                bind uu____885
                  (fun uu____894  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____908  ->
                               match uu____908 with
                               | { main_context = uu____917;
                                   main_goal = uu____918;
                                   all_implicits = uu____919;
                                   goals = sub_goals_f;
                                   smt_goals = uu____921;
                                   transaction = uu____922;_} ->
                                   bind dismiss_all
                                     (fun uu____933  ->
                                        let uu____934 = add_goals tl1 in
                                        bind uu____934
                                          (fun uu____943  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____951 =
                                                    add_goals sub_goals_f in
                                                  bind uu____951
                                                    (fun uu____960  ->
                                                       ret
                                                         (a,
                                                           (FStar_Pervasives_Native.Some
                                                              b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____992 = t1.tac_f p in
       match uu____992 with | Failed uu____997 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____1023 =
         let uu____1028 =
           let uu____1039 = map t in cur_goal_and_rest t uu____1039 in
         bind uu____1028
           (fun uu___78_1056  ->
              match uu___78_1056 with
              | (hd1,FStar_Pervasives_Native.None ) -> ret [hd1]
              | (hd1,FStar_Pervasives_Native.Some tl1) -> ret (hd1 :: tl1)) in
       run uu____1023 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal "map_goal"
        (fun g  ->
           let uu____1108 =
             let uu___90_1109 = g in
             let uu____1110 = f g.goal_ty in
             {
               context = (uu___90_1109.context);
               witness = (uu___90_1109.witness);
               goal_ty = uu____1110
             } in
           replace_cur uu____1108) in
    let uu____1111 = map aux in bind uu____1111 (fun uu____1118  -> ret ())
let map_meta t =
  with_cur_goal "map_meta"
    (fun g  ->
       let uu____1135 =
         let uu____1136 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____1136.FStar_Syntax_Syntax.n in
       match uu____1135 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____1153 =
             replace_cur
               (let uu___91_1156 = g in
                {
                  context = (uu___91_1156.context);
                  witness = (uu___91_1156.witness);
                  goal_ty = f
                }) in
           bind uu____1153
             (fun uu____1157  ->
                bind t
                  (fun a  ->
                     let uu____1159 =
                       map_goal_term
                         (fun tm  ->
                            let uu____1163 = is_true tm in
                            if uu____1163
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                FStar_Pervasives_Native.None
                                tm.FStar_Syntax_Syntax.pos) in
                     bind uu____1159 (fun uu____1165  -> ret a)))
       | uu____1166 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1185 =
        bind t1
          (fun uu____1188  ->
             let uu____1189 = map t2 in
             bind uu____1189 (fun uu____1196  -> ret ())) in
      focus_cur_goal "seq" uu____1185
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal "intros"
    (fun goal  ->
       let uu____1202 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1202 with
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (bs,pats,body))
           ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             {
               context = new_context;
               witness = FStar_Pervasives_Native.None;
               goal_ty = body
             } in
           bind dismiss
             (fun uu____1212  ->
                let uu____1213 = add_goals [new_goal] in
                bind uu____1213
                  (fun uu____1216  ->
                     let uu____1217 =
                       FStar_All.pipe_left mlog
                         (fun uu____1224  ->
                            let uu____1225 =
                              FStar_Syntax_Print.binders_to_string ", " bs in
                            FStar_Util.print1 "intros: %s\n" uu____1225) in
                     bind uu____1217 (fun uu____1226  -> ret bs)))
       | uu____1227 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____1232  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Parser_Const.squash_lid in
  let uu____1245 =
    let uu____1256 = FStar_Syntax_Syntax.as_arg p in [uu____1256] in
  FStar_Syntax_Util.mk_app sq uu____1245
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____1266 = FStar_Syntax_Util.head_and_args t in
    match uu____1266 with
    | (head1,args) ->
        let uu____1321 =
          let uu____1336 =
            let uu____1337 = FStar_Syntax_Util.un_uinst head1 in
            uu____1337.FStar_Syntax_Syntax.n in
          (uu____1336, args) in
        (match uu____1321 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____1360)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1399;
               FStar_Syntax_Syntax.index = uu____1400;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1402;
                   FStar_Syntax_Syntax.pos = uu____1403;
                   FStar_Syntax_Syntax.vars = uu____1404;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
             FStar_Pervasives_Native.Some p
         | uu____1440 -> FStar_Pervasives_Native.None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal "imp_intro"
    (fun goal  ->
       let uu____1462 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1462 with
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1469)::(rhs,uu____1471)::[])) when
           FStar_Ident.lid_equals l FStar_Parser_Const.imp_lid ->
           let name =
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None lhs in
           let new_goal =
             let uu____1524 = FStar_TypeChecker_Env.push_bv goal.context name in
             {
               context = uu____1524;
               witness = FStar_Pervasives_Native.None;
               goal_ty = rhs
             } in
           bind dismiss
             (fun uu____1525  ->
                let uu____1526 = add_goals [new_goal] in
                bind uu____1526
                  (fun uu____1529  ->
                     let uu____1530 =
                       FStar_All.pipe_left mlog
                         (fun uu____1537  ->
                            let uu____1538 =
                              FStar_Syntax_Print.bv_to_string name in
                            FStar_Util.print1 "imp_intro: %s\n" uu____1538) in
                     bind uu____1530
                       (fun uu____1539  ->
                          let uu____1540 = FStar_Syntax_Syntax.mk_binder name in
                          ret uu____1540)))
       | uu____1541 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal "split"
    (fun goal  ->
       let uu____1547 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1547 with
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (l,args))
           when FStar_Ident.lid_equals l FStar_Parser_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1563  ->
                     match uu____1563 with
                     | (a,uu____1569) ->
                         let uu___92_1570 = goal in
                         {
                           context = (uu___92_1570.context);
                           witness = FStar_Pervasives_Native.None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1571  -> add_goals new_goals)
       | uu____1572 -> fail "Cannot split this goal; expected a conjunction")
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
       let uu____1582 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1582 with
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (l,[]))
           when FStar_Ident.lid_equals l FStar_Parser_Const.true_lid ->
           bind dismiss
             (fun uu____1606  ->
                add_goals
                  [(let uu___93_1607 = goal in
                    {
                      context = (uu___93_1607.context);
                      witness = (uu___93_1607.witness);
                      goal_ty = t
                    })])
       | uu____1608 -> fail "Not a trivial goal")
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "apply_lemma"
      (fun goal  ->
         try
           let uu____1624 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1624 with
           | (tm1,t,guard) ->
               let uu____1636 =
                 let uu____1637 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1637 in
               if uu____1636
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1641 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1641 with
                  | (bs,comp) ->
                      let uu____1668 =
                        FStar_List.fold_left
                          (fun uu____1701  ->
                             fun uu____1702  ->
                               match (uu____1701, uu____1702) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1793 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1793 with
                                    | (u,uu____1821,g_u) ->
                                        let uu____1835 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1835,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1668 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1893 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1921 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____1980 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1893 with
                            | (pre,post) ->
                                let uu____2023 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____2023 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail
                                       "apply_lemma: does not unify with goal"
                                 | FStar_Pervasives_Native.Some g ->
                                     let g1 =
                                       let uu____2030 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____2030
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____2091  ->
                                               match uu____2091 with
                                               | (uu____2104,uu____2105,uu____2106,tm2,uu____2108,uu____2109)
                                                   ->
                                                   let uu____2110 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____2110 with
                                                    | (hd1,uu____2130) ->
                                                        let uu____2159 =
                                                          let uu____2160 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____2160.FStar_Syntax_Syntax.n in
                                                        (match uu____2159
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____2165 ->
                                                             true
                                                         | uu____2182 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____2187 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____2218  ->
                                                   match uu____2218 with
                                                   | (_msg,_env,_uvar,term,typ,uu____2236)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (FStar_Pervasives_Native.Some
                                                              term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___96_2237 = goal in
                                          {
                                            context = (uu___96_2237.context);
                                            witness =
                                              FStar_Pervasives_Native.None;
                                            goal_ty = pre
                                          }) :: uu____2187 in
                                       let uu____2238 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____2238
                                         (fun uu____2241  ->
                                            bind dismiss
                                              (fun uu____2242  ->
                                                 add_goals sub_goals))))))))
         with | uu____2246 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "exact"
      (fun goal  ->
         try
           let uu____2260 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____2260 with
           | (uu____2269,t,guard) ->
               let uu____2272 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____2272
               then
                 (solve goal tm;
                  replace_cur
                    (let uu___99_2276 = goal in
                     {
                       context = (uu___99_2276.context);
                       witness = FStar_Pervasives_Native.None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____2279 = FStar_Syntax_Print.term_to_string tm in
                    let uu____2280 = FStar_Syntax_Print.term_to_string t in
                    let uu____2281 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____2279
                      uu____2280 uu____2281 in
                  fail msg)
         with
         | e ->
             let uu____2286 =
               let uu____2287 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____2287 in
             fail uu____2286)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal "rewrite"
      (fun goal  ->
         let uu____2296 =
           FStar_All.pipe_left mlog
             (fun uu____2303  ->
                let uu____2304 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h) in
                let uu____2305 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2304
                  uu____2305) in
         bind uu____2296
           (fun uu____2306  ->
              let uu____2307 =
                let uu____2310 =
                  let uu____2311 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h) in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____2311 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2310 in
              match uu____2307 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2323::(x,uu____2325)::(e,uu____2327)::[])) when
                  FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
                  let uu____2394 =
                    let uu____2395 = FStar_Syntax_Subst.compress x in
                    uu____2395.FStar_Syntax_Syntax.n in
                  (match uu____2394 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___100_2404 = goal in
                         let uu____2405 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___100_2404.context);
                           witness = (uu___100_2404.witness);
                           goal_ty = uu____2405
                         } in
                       replace_cur goal1
                   | uu____2410 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2411 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal "clear"
    (fun goal  ->
       let uu____2417 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2417 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____2439 = FStar_Util.set_mem x fns in
           if uu____2439
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___101_2444 = goal in
                {
                  context = env';
                  witness = (uu___101_2444.witness);
                  goal_ty = (uu___101_2444.goal_ty)
                } in
              bind dismiss (fun uu____2445  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "clear_hd"
      (fun goal  ->
         let uu____2454 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2454 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal "revert"
    (fun goal  ->
       let uu____2479 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2479 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____2502 = FStar_Util.set_mem x fvs in
             if uu____2502
             then
               let uu___102_2503 = goal in
               let uu____2504 =
                 let uu____2505 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____2505 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___102_2503.witness);
                 goal_ty = uu____2504
               }
             else
               (let uu___103_2507 = goal in
                let uu____2508 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___103_2507.witness);
                  goal_ty = uu____2508
                }) in
           bind dismiss (fun uu____2509  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "revert_hd"
      (fun goal  ->
         let uu____2518 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2518 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2539 =
                 let uu____2540 = FStar_Syntax_Print.bv_to_string x in
                 let uu____2541 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____2540 uu____2541 in
               fail uu____2539
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2560 = revert_all_hd xs1 in
        bind uu____2560 (fun uu____2563  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____2567 =
      let uu____2568 = FStar_Syntax_Subst.compress x in
      uu____2568.FStar_Syntax_Syntax.n in
    match uu____2567 with
    | FStar_Syntax_Syntax.Tm_name uu____2573 -> true
    | uu____2574 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____2578 =
      let uu____2579 = FStar_Syntax_Subst.compress x in
      uu____2579.FStar_Syntax_Syntax.n in
    match uu____2578 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____2585 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                              FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term',
                                                           FStar_Syntax_Syntax.term')
                                                           FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____2605 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____2605 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____2626)::(rhs,uu____2628)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.imp_lid ->
        let uu____2679 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____2679 with
         | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
             (eq1,uu____2699::(x,uu____2701)::(e,uu____2703)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Parser_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____2770 =
               let uu____2785 = as_name x in (uu____2785, e, rhs) in
             FStar_Pervasives_Native.Some uu____2770
         | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
             (eq1,(x,uu____2810)::(e,uu____2812)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Parser_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____2863 =
               let uu____2878 = as_name x in (uu____2878, e, rhs) in
             FStar_Pervasives_Native.Some uu____2863
         | uu____2901 -> FStar_Pervasives_Native.None)
    | uu____2918 -> FStar_Pervasives_Native.None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | [] -> ret a
            | uu____2952::[] -> ret a
            | uu____2953 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____2966 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____2966
           then
             let uu____2969 =
               let uu___104_2970 = p in
               let uu____2971 =
                 let uu____2974 = conj_goals g1 g2 in uu____2974 :: rest in
               {
                 main_context = (uu___104_2970.main_context);
                 main_goal = (uu___104_2970.main_goal);
                 all_implicits = (uu___104_2970.all_implicits);
                 goals = uu____2971;
                 smt_goals = (uu___104_2970.smt_goals);
                 transaction = (uu___104_2970.transaction)
               } in
             set uu____2969
           else
             (let g1_binders =
                let uu____2977 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____2977
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____2979 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____2979
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____2980 =
                let uu____2981 = goal_to_string g1 in
                let uu____2982 = goal_to_string g2 in
                let uu____2983 =
                  let uu____2984 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____2984 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____2981 uu____2982 uu____2983 in
              fail uu____2980)
       | uu____2985 ->
           let goals =
             let uu____2989 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____2989 (FStar_String.concat "\n\t") in
           let uu____2999 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____2999)
let rec visit: Prims.unit tac -> Prims.unit tac =
  fun callback  ->
    let uu____3011 =
      let uu____3014 =
        with_cur_goal "visit_strengthen_else"
          (fun goal  ->
             let uu____3018 =
               FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
             match uu____3018 with
             | FStar_Pervasives_Native.None  ->
                 let uu____3023 =
                   let uu____3024 = FStar_Syntax_Subst.compress goal.goal_ty in
                   uu____3024.FStar_Syntax_Syntax.n in
                 (match uu____3023 with
                  | FStar_Syntax_Syntax.Tm_meta uu____3031 ->
                      let uu____3040 = visit callback in map_meta uu____3040
                  | uu____3043 ->
                      let uu____3044 =
                        FStar_All.pipe_left mlog
                          (fun uu____3051  ->
                             let uu____3052 =
                               FStar_Syntax_Print.term_to_string goal.goal_ty in
                             FStar_Util.print1
                               "Not a formula, split to smt %s\n" uu____3052) in
                      bind uu____3044 (fun uu____3053  -> smt))
             | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
                 uu____3054) ->
                 let uu____3061 =
                   FStar_All.pipe_left mlog
                     (fun uu____3068  ->
                        let uu____3069 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        FStar_Util.print1
                          "Not yet handled: exists\n\tGoal is %s\n"
                          uu____3069) in
                 bind uu____3061 (fun uu____3070  -> ret ())
             | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                 (xs,uu____3072,uu____3073)) ->
                 bind intros
                   (fun binders  ->
                      let uu____3075 = visit callback in
                      let uu____3078 =
                        let uu____3081 =
                          let uu____3084 =
                            FStar_List.map FStar_Pervasives_Native.fst
                              binders in
                          revert_all_hd uu____3084 in
                        bind uu____3081
                          (fun uu____3091  ->
                             with_cur_goal "inner"
                               (fun goal1  ->
                                  let uu____3093 =
                                    FStar_All.pipe_left mlog
                                      (fun uu____3100  ->
                                         let uu____3101 =
                                           goal_to_string goal1 in
                                         FStar_Util.print1
                                           "After reverting intros, goal is %s\n"
                                           uu____3101) in
                                  bind uu____3093 (fun uu____3102  -> ret ()))) in
                      seq uu____3075 uu____3078)
             | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                 (l,uu____3104)) when
                 FStar_Ident.lid_equals l FStar_Parser_Const.and_lid ->
                 let uu____3105 =
                   let uu____3108 = visit callback in seq split uu____3108 in
                 bind uu____3105 (fun uu____3111  -> merge_sub_goals)
             | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                 (l,uu____3113)) when
                 FStar_Ident.lid_equals l FStar_Parser_Const.imp_lid ->
                 bind imp_intro
                   (fun h  ->
                      let uu____3115 = visit callback in
                      seq uu____3115 revert)
             | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                 (l,uu____3119)) -> or_else trivial smt) in
      or_else callback uu____3014 in
    focus_cur_goal "visit_strengthen" uu____3011
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____3123 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____3127 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____3131 -> false
let order_binder:
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder -> order =
  fun x  ->
    fun y  ->
      let n1 =
        FStar_Syntax_Syntax.order_bv (FStar_Pervasives_Native.fst x)
          (FStar_Pervasives_Native.fst y) in
      if n1 < (Prims.parse_int "0")
      then Lt
      else if n1 = (Prims.parse_int "0") then Eq else Gt
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> proofstate =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____3148 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        {
          context = env;
          witness = FStar_Pervasives_Native.None;
          goal_ty = uu____3148
        } in
      let uu____3149 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____3149
      }