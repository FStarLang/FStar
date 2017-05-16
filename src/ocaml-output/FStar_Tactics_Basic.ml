open Prims
type name = FStar_Syntax_Syntax.bv
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
type goal =
  {
  context: FStar_TypeChecker_Env.env;
  witness: FStar_Syntax_Syntax.term Prims.option;
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
  | Success of ('a* proofstate)
  | Failed of (Prims.string* proofstate)
let uu___is_Success projectee =
  match projectee with | Success _0 -> true | uu____103 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success _0 -> _0
let uu___is_Failed projectee =
  match projectee with | Failed _0 -> true | uu____134 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed _0 -> _0
exception Failure of Prims.string
let uu___is_Failure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Failure uu____158 -> true | uu____159 -> false
let __proj__Failure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Failure uu____166 -> uu____166
type 'a tac = {
  tac_f: proofstate -> 'a result;}
let mk_tac f = { tac_f = f }
let run t p = t.tac_f p
let ret x = mk_tac (fun p  -> Success (x, p))
let bind t1 t2 =
  mk_tac
    (fun p  ->
       let uu____259 = run t1 p in
       match uu____259 with
       | Success (a,q) -> let uu____264 = t2 a in run uu____264 q
       | Failed (msg,q) -> Failed (msg, q))
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____272 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____272
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____273 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format2 "%s |- %s" g_binders uu____273
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____283 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____283
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____293 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____293
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____306 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____306
let dump_goal ps goal =
  let uu____320 = goal_to_string goal in tacprint uu____320
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint1 "State dump (%s):" msg;
      (let uu____329 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____329);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____335 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____335);
      FStar_List.iter (dump_goal ps) ps.smt_goals
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let log ps f =
  let uu____366 = FStar_ST.read tacdbg in if uu____366 then f () else ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____392 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____392 then dump_proofstate ps "TACTING FAILING" else ());
       Failed (msg, ps))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____399  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      match goal.witness with
      | None  -> ()
      | Some w ->
          let uu____407 =
            FStar_TypeChecker_Rel.teq_nosmt goal.context w solution in
          if uu____407
          then ()
          else
            (let uu____409 =
               let uu____410 =
                 let uu____411 = FStar_Syntax_Print.term_to_string solution in
                 let uu____412 = FStar_Syntax_Print.term_to_string w in
                 let uu____413 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 FStar_Util.format3 "%s does not solve %s : %s" uu____411
                   uu____412 uu____413 in
               Failure uu____410 in
             Prims.raise uu____409)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____416 =
         let uu___83_417 = p in
         let uu____418 = FStar_List.tl p.goals in
         {
           main_context = (uu___83_417.main_context);
           main_goal = (uu___83_417.main_goal);
           all_implicits = (uu___83_417.all_implicits);
           goals = uu____418;
           smt_goals = (uu___83_417.smt_goals);
           transaction = (uu___83_417.transaction)
         } in
       set uu____416)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___84_422 = p in
          {
            main_context = (uu___84_422.main_context);
            main_goal = (uu___84_422.main_goal);
            all_implicits = (uu___84_422.all_implicits);
            goals = [];
            smt_goals = (uu___84_422.smt_goals);
            transaction = (uu___84_422.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___85_431 = p in
            {
              main_context = (uu___85_431.main_context);
              main_goal = (uu___85_431.main_goal);
              all_implicits = (uu___85_431.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___85_431.smt_goals);
              transaction = (uu___85_431.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___86_440 = p in
            {
              main_context = (uu___86_440.main_context);
              main_goal = (uu___86_440.main_goal);
              all_implicits = (uu___86_440.all_implicits);
              goals = (uu___86_440.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___86_440.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____446  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___87_453 = p in
            {
              main_context = (uu___87_453.main_context);
              main_goal = (uu___87_453.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___87_453.goals);
              smt_goals = (uu___87_453.smt_goals);
              transaction = (uu___87_453.transaction)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____463 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____463 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid
    | uu____475 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____480 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____480 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid
    | uu____492 -> false
let conj_goals: goal -> goal -> goal =
  fun g1  ->
    fun g2  ->
      let t1 = g1.goal_ty in
      let t2 = g2.goal_ty in
      let uu____502 = (is_true t1) || (is_false t2) in
      if uu____502
      then g2
      else
        (let uu____504 = (is_true t2) || (is_false t1) in
         if uu____504
         then g1
         else
           (let uu___88_506 = g1 in
            let uu____507 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___88_506.context);
              witness = (uu___88_506.witness);
              goal_ty = uu____507
            }))
let with_cur_goal f =
  bind get
    (fun p  ->
       match p.goals with | [] -> fail "No more goals" | hd1::tl1 -> f hd1)
let cur_goal: goal tac =
  mk_tac
    (fun ps  ->
       match ps.goals with
       | hd1::uu____532 -> Success (hd1, ps)
       | uu____534 -> Failed ("No goals left", ps))
let set_cur_goal: goal -> Prims.unit tac =
  fun g  ->
    mk_tac
      (fun ps  ->
         match ps.goals with
         | hd1::tl1 ->
             Success
               ((),
                 (let uu___89_546 = ps in
                  {
                    main_context = (uu___89_546.main_context);
                    main_goal = (uu___89_546.main_goal);
                    all_implicits = (uu___89_546.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___89_546.smt_goals);
                    transaction = (uu___89_546.transaction)
                  }))
         | uu____547 -> Failed ("No goals left", ps))
let replace_point:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax
  =
  fun e1  ->
    fun e2  ->
      fun t  ->
        let uu____572 = FStar_Syntax_Util.term_eq e1 t in
        if uu____572 then e2 else t
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
                 let uu____615 = FStar_TypeChecker_Rel.try_teq true env t1 t2 in
                 match uu____615 with
                 | None  -> false
                 | Some g1 -> FStar_TypeChecker_Rel.is_trivial g1 in
               if ok
               then
                 let goal_ty' = treplace env e1 e2 g.goal_ty in
                 let uu____620 =
                   set_cur_goal
                     (let uu___90_622 = g in
                      {
                        context = (uu___90_622.context);
                        witness = (uu___90_622.witness);
                        goal_ty = goal_ty'
                      }) in
                 bind uu____620
                   (fun uu____623  ->
                      let uu____624 =
                        let uu____626 =
                          let uu____627 =
                            FStar_Syntax_Util.mk_eq2
                              FStar_Syntax_Syntax.U_zero t1 e1 e2 in
                          {
                            context = (g.context);
                            witness = None;
                            goal_ty = uu____627
                          } in
                        [uu____626] in
                      add_goals uu____624)
               else
                 (FStar_TypeChecker_Err.add_errors env
                    [("Ill-type rewriting requested",
                       (e1.FStar_Syntax_Syntax.pos))];
                  fail "grewrite: Ill-typed rewriting requested"))
let smt: Prims.unit tac =
  with_cur_goal
    (fun g  -> bind dismiss (fun uu____636  -> add_smt_goals [g]))
let focus_cur_goal f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___91_653 = p in
             {
               main_context = (uu___91_653.main_context);
               main_goal = (uu___91_653.main_goal);
               all_implicits = (uu___91_653.all_implicits);
               goals = [hd1];
               smt_goals = (uu___91_653.smt_goals);
               transaction = (uu___91_653.transaction)
             } in
           let uu____654 = set q in
           bind uu____654
             (fun uu____656  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___92_660 = q' in
                            {
                              main_context = (uu___92_660.main_context);
                              main_goal = (uu___92_660.main_goal);
                              all_implicits = (uu___92_660.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___92_660.smt_goals);
                              transaction = (uu___92_660.transaction)
                            } in
                          let uu____661 = set q2 in
                          bind uu____661 (fun uu____663  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret (None, None)
       | uu____703::[] -> bind f (fun a  -> ret ((Some a), None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____722  ->
                let uu____723 = add_goals [hd1] in
                bind uu____723
                  (fun uu____729  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____739  ->
                               match uu____739 with
                               | { main_context = uu____745;
                                   main_goal = uu____746;
                                   all_implicits = uu____747;
                                   goals = sub_goals_f;
                                   smt_goals = uu____749;
                                   transaction = uu____750;_} ->
                                   bind dismiss_all
                                     (fun uu____757  ->
                                        let uu____758 = add_goals tl1 in
                                        bind uu____758
                                          (fun uu____764  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____770 =
                                                    add_goals sub_goals_f in
                                                  bind uu____770
                                                    (fun uu____776  ->
                                                       ret
                                                         ((Some a), (Some b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____801 = t1.tac_f p in
       match uu____801 with | Failed uu____804 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____822 =
         let uu____825 =
           let uu____832 = map t in cur_goal_and_rest t uu____832 in
         bind uu____825
           (fun uu___82_842  ->
              match uu___82_842 with
              | (None ,None ) -> ret []
              | (Some hd1,None ) -> ret [hd1]
              | (Some hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____822 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal
        (fun g  ->
           let uu____883 =
             let uu___93_884 = g in
             let uu____885 = f g.goal_ty in
             {
               context = (uu___93_884.context);
               witness = (uu___93_884.witness);
               goal_ty = uu____885
             } in
           replace_cur uu____883) in
    let uu____886 = map aux in bind uu____886 (fun uu____890  -> ret ())
let map_meta t =
  with_cur_goal
    (fun g  ->
       let uu____903 =
         let uu____904 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____904.FStar_Syntax_Syntax.n in
       match uu____903 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____914 =
             replace_cur
               (let uu___94_916 = g in
                {
                  context = (uu___94_916.context);
                  witness = (uu___94_916.witness);
                  goal_ty = f
                }) in
           bind uu____914
             (fun uu____917  ->
                bind t
                  (fun a  ->
                     let uu____919 =
                       map_goal_term
                         (fun tm  ->
                            let uu____922 = is_true tm in
                            if uu____922
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____919 (fun uu____928  -> ret a)))
       | uu____929 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____942 =
        bind t1
          (fun uu____944  ->
             let uu____945 = map t2 in
             bind uu____945 (fun uu____949  -> ret ())) in
      focus_cur_goal uu____942
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal
    (fun goal  ->
       let uu____953 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____953 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____961  ->
                let uu____962 = add_goals [new_goal] in
                bind uu____962
                  (fun uu____964  ->
                     let uu____965 =
                       FStar_All.pipe_left mlog
                         (fun uu____970  ->
                            let uu____971 =
                              FStar_Syntax_Print.binders_to_string ", " bs in
                            FStar_Util.print1 "intros: %s\n" uu____971) in
                     bind uu____965 (fun uu____972  -> ret bs)))
       | uu____973 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____976  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____987 = let uu____993 = FStar_Syntax_Syntax.as_arg p in [uu____993] in
  FStar_Syntax_Util.mk_app sq uu____987
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____1000 = FStar_Syntax_Util.head_and_args t in
    match uu____1000 with
    | (head1,args) ->
        let uu____1029 =
          let uu____1037 =
            let uu____1038 = FStar_Syntax_Util.un_uinst head1 in
            uu____1038.FStar_Syntax_Syntax.n in
          (uu____1037, args) in
        (match uu____1029 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____1051)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1071;
               FStar_Syntax_Syntax.index = uu____1072;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1074;
                   FStar_Syntax_Syntax.pos = uu____1075;
                   FStar_Syntax_Syntax.vars = uu____1076;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____1095 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal
    (fun goal  ->
       let uu____1107 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1107 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1112)::(rhs,uu____1114)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1142 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1142; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1143  ->
                let uu____1144 = add_goals [new_goal] in
                bind uu____1144
                  (fun uu____1146  ->
                     let uu____1147 =
                       FStar_All.pipe_left mlog
                         (fun uu____1152  ->
                            let uu____1153 =
                              FStar_Syntax_Print.bv_to_string name in
                            FStar_Util.print1 "imp_intro: %s\n" uu____1153) in
                     bind uu____1147
                       (fun uu____1154  ->
                          let uu____1155 = FStar_Syntax_Syntax.mk_binder name in
                          ret uu____1155)))
       | uu____1156 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1160 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1160 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1170  ->
                     match uu____1170 with
                     | (a,uu____1174) ->
                         let uu___95_1175 = goal in
                         {
                           context = (uu___95_1175.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1176  -> add_goals new_goals)
       | uu____1177 -> fail "Cannot split this goal; expected a conjunction")
let trivial: Prims.unit tac =
  with_cur_goal
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
       let uu____1184 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1184 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid ->
           bind dismiss
             (fun uu____1197  ->
                add_goals
                  [(let uu___96_1198 = goal in
                    {
                      context = (uu___96_1198.context);
                      witness = (uu___96_1198.witness);
                      goal_ty = t
                    })])
       | uu____1199 -> fail "Not a trivial goal")
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1210 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1210 with
           | (tm1,t,guard) ->
               let uu____1218 =
                 let uu____1219 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1219 in
               if uu____1218
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1222 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1222 with
                  | (bs,comp) ->
                      let uu____1237 =
                        FStar_List.fold_left
                          (fun uu____1254  ->
                             fun uu____1255  ->
                               match (uu____1254, uu____1255) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1304 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1304 with
                                    | (u,uu____1319,g_u) ->
                                        let uu____1327 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1327,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1237 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1359 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1375 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1405 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1359 with
                            | (pre,post) ->
                                let uu____1428 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1428 with
                                 | None  ->
                                     fail
                                       "apply_lemma: does not unify with goal"
                                 | Some g ->
                                     let g1 =
                                       let uu____1433 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1433
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1469  ->
                                               match uu____1469 with
                                               | (uu____1476,uu____1477,uu____1478,tm2,uu____1480,uu____1481)
                                                   ->
                                                   let uu____1482 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1482 with
                                                    | (hd1,uu____1493) ->
                                                        let uu____1508 =
                                                          let uu____1509 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1509.FStar_Syntax_Syntax.n in
                                                        (match uu____1508
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1512 ->
                                                             true
                                                         | uu____1521 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____1525 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____1541  ->
                                                   match uu____1541 with
                                                   | (_msg,_env,_uvar,term,typ,uu____1553)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (Some term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___99_1554 = goal in
                                          {
                                            context = (uu___99_1554.context);
                                            witness = None;
                                            goal_ty = pre
                                          }) :: uu____1525 in
                                       let uu____1555 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1555
                                         (fun uu____1557  ->
                                            bind dismiss
                                              (fun uu____1558  ->
                                                 add_goals sub_goals))))))))
         with | uu____1561 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1571 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1571 with
           | (uu____1576,t,guard) ->
               let uu____1579 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1579
               then
                 (solve goal tm;
                  replace_cur
                    (let uu___102_1582 = goal in
                     {
                       context = (uu___102_1582.context);
                       witness = None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____1585 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1586 = FStar_Syntax_Print.term_to_string t in
                    let uu____1587 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1585
                      uu____1586 uu____1587 in
                  fail msg)
         with
         | e ->
             let uu____1591 =
               let uu____1592 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1592 in
             fail uu____1591)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal
      (fun goal  ->
         let uu____1599 =
           FStar_All.pipe_left mlog
             (fun uu____1604  ->
                let uu____1605 =
                  FStar_Syntax_Print.bv_to_string (Prims.fst h) in
                let uu____1606 =
                  FStar_Syntax_Print.term_to_string
                    (Prims.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1605
                  uu____1606) in
         bind uu____1599
           (fun uu____1607  ->
              let uu____1608 =
                let uu____1610 =
                  let uu____1611 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (Prims.fst h) in
                  FStar_All.pipe_left Prims.fst uu____1611 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1610 in
              match uu____1608 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1618::(x,uu____1620)::(e,uu____1622)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____1656 =
                    let uu____1657 = FStar_Syntax_Subst.compress x in
                    uu____1657.FStar_Syntax_Syntax.n in
                  (match uu____1656 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___103_1663 = goal in
                         let uu____1664 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___103_1663.context);
                           witness = (uu___103_1663.witness);
                           goal_ty = uu____1664
                         } in
                       replace_cur goal1
                   | uu____1667 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____1668 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1672 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1672 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1685 = FStar_Util.set_mem x fns in
           if uu____1685
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___104_1689 = goal in
                {
                  context = env';
                  witness = (uu___104_1689.witness);
                  goal_ty = (uu___104_1689.goal_ty)
                } in
              bind dismiss (fun uu____1690  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1697 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1697 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1712 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1712 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1726 = FStar_Util.set_mem x fvs in
             if uu____1726
             then
               let uu___105_1727 = goal in
               let uu____1728 =
                 let uu____1729 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1729 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___105_1727.witness);
                 goal_ty = uu____1728
               }
             else
               (let uu___106_1731 = goal in
                let uu____1732 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___106_1731.witness);
                  goal_ty = uu____1732
                }) in
           bind dismiss (fun uu____1733  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1740 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1740 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1752 =
                 let uu____1753 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1754 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1753 uu____1754 in
               fail uu____1752
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1767 = revert_all_hd xs1 in
        bind uu____1767 (fun uu____1769  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1773 =
      let uu____1774 = FStar_Syntax_Subst.compress x in
      uu____1774.FStar_Syntax_Syntax.n in
    match uu____1773 with
    | FStar_Syntax_Syntax.Tm_name uu____1777 -> true
    | uu____1778 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1782 =
      let uu____1783 = FStar_Syntax_Subst.compress x in
      uu____1783.FStar_Syntax_Syntax.n in
    match uu____1782 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1787 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun t  ->
    let uu____1799 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1799 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____1811)::(rhs,uu____1813)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____1839 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____1839 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____1911 =
               let uu____1919 = as_name x in (uu____1919, e, rhs) in
             Some uu____1911
         | uu____1931 -> None)
    | uu____1940 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____1963 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____1972 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____1972
           then
             let uu____1974 =
               let uu___107_1975 = p in
               let uu____1976 =
                 let uu____1978 = conj_goals g1 g2 in uu____1978 :: rest in
               {
                 main_context = (uu___107_1975.main_context);
                 main_goal = (uu___107_1975.main_goal);
                 all_implicits = (uu___107_1975.all_implicits);
                 goals = uu____1976;
                 smt_goals = (uu___107_1975.smt_goals);
                 transaction = (uu___107_1975.transaction)
               } in
             set uu____1974
           else
             (let g1_binders =
                let uu____1981 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____1981
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____1983 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____1983
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____1984 =
                let uu____1985 = goal_to_string g1 in
                let uu____1986 = goal_to_string g2 in
                let uu____1987 =
                  let uu____1988 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____1988 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____1985 uu____1986 uu____1987 in
              fail uu____1984)
       | uu____1989 ->
           let goals =
             let uu____1992 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____1992 (FStar_String.concat "\n\t") in
           let uu____1998 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____1998)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___108_2008 = g in
           {
             context = ctx';
             witness = (uu___108_2008.witness);
             goal_ty = (uu___108_2008.goal_ty)
           } in
         bind dismiss (fun uu____2009  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___109_2019 = g in
           {
             context = ctx';
             witness = (uu___109_2019.witness);
             goal_ty = (uu___109_2019.goal_ty)
           } in
         bind dismiss (fun uu____2020  -> add_goals [g']))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2024 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2028 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2032 -> false
let order_binder:
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder -> order =
  fun x  ->
    fun y  ->
      let n1 = FStar_Syntax_Syntax.order_bv (Prims.fst x) (Prims.fst y) in
      if n1 < (Prims.parse_int "0")
      then Lt
      else if n1 = (Prims.parse_int "0") then Eq else Gt
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> proofstate =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____2049 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2049 } in
      let uu____2050 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2050
      }