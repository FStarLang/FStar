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
         let uu___80_417 = p in
         let uu____418 = FStar_List.tl p.goals in
         {
           main_context = (uu___80_417.main_context);
           main_goal = (uu___80_417.main_goal);
           all_implicits = (uu___80_417.all_implicits);
           goals = uu____418;
           smt_goals = (uu___80_417.smt_goals);
           transaction = (uu___80_417.transaction)
         } in
       set uu____416)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___81_422 = p in
          {
            main_context = (uu___81_422.main_context);
            main_goal = (uu___81_422.main_goal);
            all_implicits = (uu___81_422.all_implicits);
            goals = [];
            smt_goals = (uu___81_422.smt_goals);
            transaction = (uu___81_422.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_431 = p in
            {
              main_context = (uu___82_431.main_context);
              main_goal = (uu___82_431.main_goal);
              all_implicits = (uu___82_431.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___82_431.smt_goals);
              transaction = (uu___82_431.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_440 = p in
            {
              main_context = (uu___83_440.main_context);
              main_goal = (uu___83_440.main_goal);
              all_implicits = (uu___83_440.all_implicits);
              goals = (uu___83_440.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___83_440.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____446  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_453 = p in
            {
              main_context = (uu___84_453.main_context);
              main_goal = (uu___84_453.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_453.goals);
              smt_goals = (uu___84_453.smt_goals);
              transaction = (uu___84_453.transaction)
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
           (let uu___85_506 = g1 in
            let uu____507 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___85_506.context);
              witness = (uu___85_506.witness);
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
                 (let uu___86_546 = ps in
                  {
                    main_context = (uu___86_546.main_context);
                    main_goal = (uu___86_546.main_goal);
                    all_implicits = (uu___86_546.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___86_546.smt_goals);
                    transaction = (uu___86_546.transaction)
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
                     (let uu___87_622 = g in
                      {
                        context = (uu___87_622.context);
                        witness = (uu___87_622.witness);
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
             let uu___88_653 = p in
             {
               main_context = (uu___88_653.main_context);
               main_goal = (uu___88_653.main_goal);
               all_implicits = (uu___88_653.all_implicits);
               goals = [hd1];
               smt_goals = (uu___88_653.smt_goals);
               transaction = (uu___88_653.transaction)
             } in
           let uu____654 = set q in
           bind uu____654
             (fun uu____656  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___89_660 = q' in
                            {
                              main_context = (uu___89_660.main_context);
                              main_goal = (uu___89_660.main_goal);
                              all_implicits = (uu___89_660.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___89_660.smt_goals);
                              transaction = (uu___89_660.transaction)
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
           (fun uu___79_842  ->
              match uu___79_842 with
              | (None ,None ) -> ret []
              | (None ,Some uu____855) -> failwith "impossible"
              | (Some hd1,None ) -> ret [hd1]
              | (Some hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____822 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal
        (fun g  ->
           let uu____891 =
             let uu___90_892 = g in
             let uu____893 = f g.goal_ty in
             {
               context = (uu___90_892.context);
               witness = (uu___90_892.witness);
               goal_ty = uu____893
             } in
           replace_cur uu____891) in
    let uu____894 = map aux in bind uu____894 (fun uu____898  -> ret ())
let map_meta t =
  with_cur_goal
    (fun g  ->
       let uu____911 =
         let uu____912 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____912.FStar_Syntax_Syntax.n in
       match uu____911 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____922 =
             replace_cur
               (let uu___91_924 = g in
                {
                  context = (uu___91_924.context);
                  witness = (uu___91_924.witness);
                  goal_ty = f
                }) in
           bind uu____922
             (fun uu____925  ->
                bind t
                  (fun a  ->
                     let uu____927 =
                       map_goal_term
                         (fun tm  ->
                            let uu____930 = is_true tm in
                            if uu____930
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____927 (fun uu____936  -> ret a)))
       | uu____937 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____950 =
        bind t1
          (fun uu____952  ->
             let uu____953 = map t2 in
             bind uu____953 (fun uu____957  -> ret ())) in
      focus_cur_goal uu____950
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal
    (fun goal  ->
       let uu____961 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____961 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____969  ->
                let uu____970 = add_goals [new_goal] in
                bind uu____970
                  (fun uu____972  ->
                     let uu____973 =
                       FStar_All.pipe_left mlog
                         (fun uu____978  ->
                            let uu____979 =
                              FStar_Syntax_Print.binders_to_string ", " bs in
                            FStar_Util.print1 "intros: %s\n" uu____979) in
                     bind uu____973 (fun uu____980  -> ret bs)))
       | uu____981 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____984  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____995 =
    let uu____1001 = FStar_Syntax_Syntax.as_arg p in [uu____1001] in
  FStar_Syntax_Util.mk_app sq uu____995
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____1008 = FStar_Syntax_Util.head_and_args t in
    match uu____1008 with
    | (head1,args) ->
        let uu____1037 =
          let uu____1045 =
            let uu____1046 = FStar_Syntax_Util.un_uinst head1 in
            uu____1046.FStar_Syntax_Syntax.n in
          (uu____1045, args) in
        (match uu____1037 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____1059)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1079;
               FStar_Syntax_Syntax.index = uu____1080;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1082;
                   FStar_Syntax_Syntax.pos = uu____1083;
                   FStar_Syntax_Syntax.vars = uu____1084;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____1103 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal
    (fun goal  ->
       let uu____1115 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1115 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1120)::(rhs,uu____1122)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1150 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1150; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1151  ->
                let uu____1152 = add_goals [new_goal] in
                bind uu____1152
                  (fun uu____1154  ->
                     let uu____1155 =
                       FStar_All.pipe_left mlog
                         (fun uu____1160  ->
                            let uu____1161 =
                              FStar_Syntax_Print.bv_to_string name in
                            FStar_Util.print1 "imp_intro: %s\n" uu____1161) in
                     bind uu____1155
                       (fun uu____1162  ->
                          let uu____1163 = FStar_Syntax_Syntax.mk_binder name in
                          ret uu____1163)))
       | uu____1164 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1168 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1168 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1178  ->
                     match uu____1178 with
                     | (a,uu____1182) ->
                         let uu___92_1183 = goal in
                         {
                           context = (uu___92_1183.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1184  -> add_goals new_goals)
       | uu____1185 -> fail "Cannot split this goal; expected a conjunction")
let simpl: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops;
         FStar_TypeChecker_Normalize.Simplify] in
       let t =
         FStar_TypeChecker_Normalize.normalize steps goal.context
           goal.goal_ty in
       replace_cur
         (let uu___93_1192 = goal in
          {
            context = (uu___93_1192.context);
            witness = (uu___93_1192.witness);
            goal_ty = t
          }))
let trivial: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Primops] in
       let t =
         FStar_TypeChecker_Normalize.normalize steps goal.context
           goal.goal_ty in
       let uu____1198 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1198 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid ->
           bind dismiss
             (fun uu____1211  ->
                add_goals
                  [(let uu___94_1212 = goal in
                    {
                      context = (uu___94_1212.context);
                      witness = (uu___94_1212.witness);
                      goal_ty = t
                    })])
       | uu____1213 -> fail "Not a trivial goal")
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1224 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1224 with
           | (tm1,t,guard) ->
               let uu____1232 =
                 let uu____1233 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1233 in
               if uu____1232
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1236 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1236 with
                  | (bs,comp) ->
                      let uu____1251 =
                        FStar_List.fold_left
                          (fun uu____1268  ->
                             fun uu____1269  ->
                               match (uu____1268, uu____1269) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1318 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1318 with
                                    | (u,uu____1333,g_u) ->
                                        let uu____1341 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1341,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1251 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1373 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1389 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1419 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1373 with
                            | (pre,post) ->
                                let uu____1442 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1442 with
                                 | None  ->
                                     fail
                                       "apply_lemma: does not unify with goal"
                                 | Some g ->
                                     let g1 =
                                       let uu____1447 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1447
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1483  ->
                                               match uu____1483 with
                                               | (uu____1490,uu____1491,uu____1492,tm2,uu____1494,uu____1495)
                                                   ->
                                                   let uu____1496 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1496 with
                                                    | (hd1,uu____1507) ->
                                                        let uu____1522 =
                                                          let uu____1523 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1523.FStar_Syntax_Syntax.n in
                                                        (match uu____1522
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1526 ->
                                                             true
                                                         | uu____1535 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____1539 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____1555  ->
                                                   match uu____1555 with
                                                   | (_msg,_env,_uvar,term,typ,uu____1567)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (Some term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___97_1568 = goal in
                                          {
                                            context = (uu___97_1568.context);
                                            witness = None;
                                            goal_ty = pre
                                          }) :: uu____1539 in
                                       let uu____1569 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1569
                                         (fun uu____1571  ->
                                            bind dismiss
                                              (fun uu____1572  ->
                                                 add_goals sub_goals))))))))
         with | uu____1575 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1585 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1585 with
           | (uu____1590,t,guard) ->
               let uu____1593 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1593
               then
                 (solve goal tm;
                  replace_cur
                    (let uu___100_1596 = goal in
                     {
                       context = (uu___100_1596.context);
                       witness = None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____1599 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1600 = FStar_Syntax_Print.term_to_string t in
                    let uu____1601 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1599
                      uu____1600 uu____1601 in
                  fail msg)
         with
         | e ->
             let uu____1605 =
               let uu____1606 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1606 in
             fail uu____1605)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal
      (fun goal  ->
         let uu____1613 =
           FStar_All.pipe_left mlog
             (fun uu____1618  ->
                let uu____1619 =
                  FStar_Syntax_Print.bv_to_string (Prims.fst h) in
                let uu____1620 =
                  FStar_Syntax_Print.term_to_string
                    (Prims.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1619
                  uu____1620) in
         bind uu____1613
           (fun uu____1621  ->
              let uu____1622 =
                let uu____1624 =
                  let uu____1625 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (Prims.fst h) in
                  FStar_All.pipe_left Prims.fst uu____1625 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1624 in
              match uu____1622 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1632::(x,uu____1634)::(e,uu____1636)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____1670 =
                    let uu____1671 = FStar_Syntax_Subst.compress x in
                    uu____1671.FStar_Syntax_Syntax.n in
                  (match uu____1670 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___101_1677 = goal in
                         let uu____1678 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___101_1677.context);
                           witness = (uu___101_1677.witness);
                           goal_ty = uu____1678
                         } in
                       replace_cur goal1
                   | uu____1681 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____1682 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1686 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1686 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1699 = FStar_Util.set_mem x fns in
           if uu____1699
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___102_1703 = goal in
                {
                  context = env';
                  witness = (uu___102_1703.witness);
                  goal_ty = (uu___102_1703.goal_ty)
                } in
              bind dismiss (fun uu____1704  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1711 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1711 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1726 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1726 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1740 = FStar_Util.set_mem x fvs in
             if uu____1740
             then
               let uu___103_1741 = goal in
               let uu____1742 =
                 let uu____1743 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1743 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___103_1741.witness);
                 goal_ty = uu____1742
               }
             else
               (let uu___104_1745 = goal in
                let uu____1746 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___104_1745.witness);
                  goal_ty = uu____1746
                }) in
           bind dismiss (fun uu____1747  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1754 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1754 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1766 =
                 let uu____1767 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1768 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1767 uu____1768 in
               fail uu____1766
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1781 = revert_all_hd xs1 in
        bind uu____1781 (fun uu____1783  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1787 =
      let uu____1788 = FStar_Syntax_Subst.compress x in
      uu____1788.FStar_Syntax_Syntax.n in
    match uu____1787 with
    | FStar_Syntax_Syntax.Tm_name uu____1791 -> true
    | uu____1792 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1796 =
      let uu____1797 = FStar_Syntax_Subst.compress x in
      uu____1797.FStar_Syntax_Syntax.n in
    match uu____1796 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1801 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun t  ->
    let uu____1813 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1813 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____1825)::(rhs,uu____1827)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____1853 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____1853 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____1925 =
               let uu____1933 = as_name x in (uu____1933, e, rhs) in
             Some uu____1925
         | uu____1945 -> None)
    | uu____1954 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____1977 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____1986 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____1986
           then
             let uu____1988 =
               let uu___105_1989 = p in
               let uu____1990 =
                 let uu____1992 = conj_goals g1 g2 in uu____1992 :: rest in
               {
                 main_context = (uu___105_1989.main_context);
                 main_goal = (uu___105_1989.main_goal);
                 all_implicits = (uu___105_1989.all_implicits);
                 goals = uu____1990;
                 smt_goals = (uu___105_1989.smt_goals);
                 transaction = (uu___105_1989.transaction)
               } in
             set uu____1988
           else
             (let g1_binders =
                let uu____1995 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____1995
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____1997 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____1997
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____1998 =
                let uu____1999 = goal_to_string g1 in
                let uu____2000 = goal_to_string g2 in
                let uu____2001 =
                  let uu____2002 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____2002 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____1999 uu____2000 uu____2001 in
              fail uu____1998)
       | uu____2003 ->
           let goals =
             let uu____2006 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____2006 (FStar_String.concat "\n\t") in
           let uu____2012 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____2012)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___106_2022 = g in
           {
             context = ctx';
             witness = (uu___106_2022.witness);
             goal_ty = (uu___106_2022.goal_ty)
           } in
         bind dismiss (fun uu____2023  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___107_2033 = g in
           {
             context = ctx';
             witness = (uu___107_2033.witness);
             goal_ty = (uu___107_2033.goal_ty)
           } in
         bind dismiss (fun uu____2034  -> add_goals [g']))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2038 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2042 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2046 -> false
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
        let uu____2063 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2063 } in
      let uu____2064 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2064
      }