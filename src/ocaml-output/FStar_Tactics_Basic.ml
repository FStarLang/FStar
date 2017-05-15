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
         let uu___82_417 = p in
         let uu____418 = FStar_List.tl p.goals in
         {
           main_context = (uu___82_417.main_context);
           main_goal = (uu___82_417.main_goal);
           all_implicits = (uu___82_417.all_implicits);
           goals = uu____418;
           smt_goals = (uu___82_417.smt_goals);
           transaction = (uu___82_417.transaction)
         } in
       set uu____416)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___83_422 = p in
          {
            main_context = (uu___83_422.main_context);
            main_goal = (uu___83_422.main_goal);
            all_implicits = (uu___83_422.all_implicits);
            goals = [];
            smt_goals = (uu___83_422.smt_goals);
            transaction = (uu___83_422.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_431 = p in
            {
              main_context = (uu___84_431.main_context);
              main_goal = (uu___84_431.main_goal);
              all_implicits = (uu___84_431.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___84_431.smt_goals);
              transaction = (uu___84_431.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___85_440 = p in
            {
              main_context = (uu___85_440.main_context);
              main_goal = (uu___85_440.main_goal);
              all_implicits = (uu___85_440.all_implicits);
              goals = (uu___85_440.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___85_440.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____446  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___86_453 = p in
            {
              main_context = (uu___86_453.main_context);
              main_goal = (uu___86_453.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___86_453.goals);
              smt_goals = (uu___86_453.smt_goals);
              transaction = (uu___86_453.transaction)
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
           (let uu___87_506 = g1 in
            let uu____507 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___87_506.context);
              witness = (uu___87_506.witness);
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
                 (let uu___88_546 = ps in
                  {
                    main_context = (uu___88_546.main_context);
                    main_goal = (uu___88_546.main_goal);
                    all_implicits = (uu___88_546.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___88_546.smt_goals);
                    transaction = (uu___88_546.transaction)
                  }))
         | uu____547 -> Failed ("No goals left", ps))
let replace_point:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun e1  ->
    fun e2  ->
      fun t  ->
        let uu____558 = FStar_Syntax_Util.term_eq e1 t in
        if uu____558 then e2 else t
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
                 let uu____599 = FStar_TypeChecker_Rel.try_teq true env t1 t2 in
                 match uu____599 with
                 | None  -> false
                 | Some g1 -> FStar_TypeChecker_Rel.is_trivial g1 in
               if ok
               then
                 let goal_ty' = treplace env e1 e2 g.goal_ty in
                 let uu____604 =
                   set_cur_goal
                     (let uu___89_606 = g in
                      {
                        context = (uu___89_606.context);
                        witness = (uu___89_606.witness);
                        goal_ty = goal_ty'
                      }) in
                 bind uu____604
                   (fun uu____607  ->
                      let uu____608 =
                        let uu____610 =
                          let uu____611 =
                            FStar_Syntax_Util.mk_eq2
                              FStar_Syntax_Syntax.U_zero t1 e1 e2 in
                          {
                            context = (g.context);
                            witness = None;
                            goal_ty = uu____611
                          } in
                        [uu____610] in
                      add_goals uu____608)
               else
                 (FStar_TypeChecker_Err.add_errors env
                    [("Ill-type rewriting requested",
                       (e1.FStar_Syntax_Syntax.pos))];
                  fail "grewrite: Ill-typed rewriting requested"))
let smt: Prims.unit tac =
  with_cur_goal
    (fun g  -> bind dismiss (fun uu____620  -> add_smt_goals [g]))
let focus_cur_goal f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___90_637 = p in
             {
               main_context = (uu___90_637.main_context);
               main_goal = (uu___90_637.main_goal);
               all_implicits = (uu___90_637.all_implicits);
               goals = [hd1];
               smt_goals = (uu___90_637.smt_goals);
               transaction = (uu___90_637.transaction)
             } in
           let uu____638 = set q in
           bind uu____638
             (fun uu____640  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___91_644 = q' in
                            {
                              main_context = (uu___91_644.main_context);
                              main_goal = (uu___91_644.main_goal);
                              all_implicits = (uu___91_644.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___91_644.smt_goals);
                              transaction = (uu___91_644.transaction)
                            } in
                          let uu____645 = set q2 in
                          bind uu____645 (fun uu____647  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret (None, None)
       | uu____687::[] -> bind f (fun a  -> ret ((Some a), None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____706  ->
                let uu____707 = add_goals [hd1] in
                bind uu____707
                  (fun uu____713  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____723  ->
                               match uu____723 with
                               | { main_context = uu____729;
                                   main_goal = uu____730;
                                   all_implicits = uu____731;
                                   goals = sub_goals_f;
                                   smt_goals = uu____733;
                                   transaction = uu____734;_} ->
                                   bind dismiss_all
                                     (fun uu____741  ->
                                        let uu____742 = add_goals tl1 in
                                        bind uu____742
                                          (fun uu____748  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____754 =
                                                    add_goals sub_goals_f in
                                                  bind uu____754
                                                    (fun uu____760  ->
                                                       ret
                                                         ((Some a), (Some b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____785 = t1.tac_f p in
       match uu____785 with | Failed uu____788 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____806 =
         let uu____809 =
           let uu____816 = map t in cur_goal_and_rest t uu____816 in
         bind uu____809
           (fun uu___81_826  ->
              match uu___81_826 with
              | (None ,None ) -> ret []
              | (Some hd1,None ) -> ret [hd1]
              | (Some hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____806 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal
        (fun g  ->
           let uu____867 =
             let uu___92_868 = g in
             let uu____869 = f g.goal_ty in
             {
               context = (uu___92_868.context);
               witness = (uu___92_868.witness);
               goal_ty = uu____869
             } in
           replace_cur uu____867) in
    let uu____870 = map aux in bind uu____870 (fun uu____874  -> ret ())
let map_meta t =
  with_cur_goal
    (fun g  ->
       let uu____887 =
         let uu____888 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____888.FStar_Syntax_Syntax.n in
       match uu____887 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____898 =
             replace_cur
               (let uu___93_900 = g in
                {
                  context = (uu___93_900.context);
                  witness = (uu___93_900.witness);
                  goal_ty = f
                }) in
           bind uu____898
             (fun uu____901  ->
                bind t
                  (fun a  ->
                     let uu____903 =
                       map_goal_term
                         (fun tm  ->
                            let uu____906 = is_true tm in
                            if uu____906
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____903 (fun uu____912  -> ret a)))
       | uu____913 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____926 =
        bind t1
          (fun uu____928  ->
             let uu____929 = map t2 in
             bind uu____929 (fun uu____933  -> ret ())) in
      focus_cur_goal uu____926
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal
    (fun goal  ->
       let uu____937 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____937 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____945  ->
                let uu____946 = add_goals [new_goal] in
                bind uu____946
                  (fun uu____948  ->
                     let uu____949 =
                       FStar_All.pipe_left mlog
                         (fun uu____954  ->
                            let uu____955 =
                              FStar_Syntax_Print.binders_to_string ", " bs in
                            FStar_Util.print1 "intros: %s\n" uu____955) in
                     bind uu____949 (fun uu____956  -> ret bs)))
       | uu____957 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____960  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____971 = let uu____977 = FStar_Syntax_Syntax.as_arg p in [uu____977] in
  FStar_Syntax_Util.mk_app sq uu____971
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____984 = FStar_Syntax_Util.head_and_args t in
    match uu____984 with
    | (head1,args) ->
        let uu____1013 =
          let uu____1021 =
            let uu____1022 = FStar_Syntax_Util.un_uinst head1 in
            uu____1022.FStar_Syntax_Syntax.n in
          (uu____1021, args) in
        (match uu____1013 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____1035)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1055;
               FStar_Syntax_Syntax.index = uu____1056;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1058;
                   FStar_Syntax_Syntax.pos = uu____1059;
                   FStar_Syntax_Syntax.vars = uu____1060;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____1079 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal
    (fun goal  ->
       let uu____1091 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1091 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1096)::(rhs,uu____1098)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1126 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1126; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1127  ->
                let uu____1128 = add_goals [new_goal] in
                bind uu____1128
                  (fun uu____1130  ->
                     let uu____1131 =
                       FStar_All.pipe_left mlog
                         (fun uu____1136  ->
                            let uu____1137 =
                              FStar_Syntax_Print.bv_to_string name in
                            FStar_Util.print1 "imp_intro: %s\n" uu____1137) in
                     bind uu____1131
                       (fun uu____1138  ->
                          let uu____1139 = FStar_Syntax_Syntax.mk_binder name in
                          ret uu____1139)))
       | uu____1140 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1144 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1144 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1154  ->
                     match uu____1154 with
                     | (a,uu____1158) ->
                         let uu___94_1159 = goal in
                         {
                           context = (uu___94_1159.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1160  -> add_goals new_goals)
       | uu____1161 -> fail "Cannot split this goal; expected a conjunction")
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
       let uu____1168 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1168 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid ->
           bind dismiss
             (fun uu____1181  ->
                add_goals
                  [(let uu___95_1182 = goal in
                    {
                      context = (uu___95_1182.context);
                      witness = (uu___95_1182.witness);
                      goal_ty = t
                    })])
       | uu____1183 -> fail "Not a trivial goal")
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1194 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1194 with
           | (tm1,t,guard) ->
               let uu____1202 =
                 let uu____1203 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1203 in
               if uu____1202
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1206 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1206 with
                  | (bs,comp) ->
                      let uu____1221 =
                        FStar_List.fold_left
                          (fun uu____1238  ->
                             fun uu____1239  ->
                               match (uu____1238, uu____1239) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1288 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1288 with
                                    | (u,uu____1303,g_u) ->
                                        let uu____1311 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1311,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1221 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1343 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1359 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1389 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1343 with
                            | (pre,post) ->
                                let uu____1412 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1412 with
                                 | None  ->
                                     fail
                                       "apply_lemma: does not unify with goal"
                                 | Some g ->
                                     let g1 =
                                       let uu____1417 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1417
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1453  ->
                                               match uu____1453 with
                                               | (uu____1460,uu____1461,uu____1462,tm2,uu____1464,uu____1465)
                                                   ->
                                                   let uu____1466 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1466 with
                                                    | (hd1,uu____1477) ->
                                                        let uu____1492 =
                                                          let uu____1493 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1493.FStar_Syntax_Syntax.n in
                                                        (match uu____1492
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1496 ->
                                                             true
                                                         | uu____1505 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____1509 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____1525  ->
                                                   match uu____1525 with
                                                   | (_msg,_env,_uvar,term,typ,uu____1537)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (Some term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___98_1538 = goal in
                                          {
                                            context = (uu___98_1538.context);
                                            witness = None;
                                            goal_ty = pre
                                          }) :: uu____1509 in
                                       let uu____1539 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1539
                                         (fun uu____1541  ->
                                            bind dismiss
                                              (fun uu____1542  ->
                                                 add_goals sub_goals))))))))
         with | uu____1545 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1555 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1555 with
           | (uu____1560,t,guard) ->
               let uu____1563 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1563
               then
                 (solve goal tm;
                  replace_cur
                    (let uu___101_1566 = goal in
                     {
                       context = (uu___101_1566.context);
                       witness = None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____1569 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1570 = FStar_Syntax_Print.term_to_string t in
                    let uu____1571 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1569
                      uu____1570 uu____1571 in
                  fail msg)
         with
         | e ->
             let uu____1575 =
               let uu____1576 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1576 in
             fail uu____1575)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal
      (fun goal  ->
         let uu____1583 =
           FStar_All.pipe_left mlog
             (fun uu____1588  ->
                let uu____1589 =
                  FStar_Syntax_Print.bv_to_string (Prims.fst h) in
                let uu____1590 =
                  FStar_Syntax_Print.term_to_string
                    (Prims.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1589
                  uu____1590) in
         bind uu____1583
           (fun uu____1591  ->
              let uu____1592 =
                let uu____1594 =
                  let uu____1595 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (Prims.fst h) in
                  FStar_All.pipe_left Prims.fst uu____1595 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1594 in
              match uu____1592 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1602::(x,uu____1604)::(e,uu____1606)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____1640 =
                    let uu____1641 = FStar_Syntax_Subst.compress x in
                    uu____1641.FStar_Syntax_Syntax.n in
                  (match uu____1640 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___102_1647 = goal in
                         let uu____1648 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___102_1647.context);
                           witness = (uu___102_1647.witness);
                           goal_ty = uu____1648
                         } in
                       replace_cur goal1
                   | uu____1651 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____1652 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1656 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1656 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1669 = FStar_Util.set_mem x fns in
           if uu____1669
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___103_1673 = goal in
                {
                  context = env';
                  witness = (uu___103_1673.witness);
                  goal_ty = (uu___103_1673.goal_ty)
                } in
              bind dismiss (fun uu____1674  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1681 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1681 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1696 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1696 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1710 = FStar_Util.set_mem x fvs in
             if uu____1710
             then
               let uu___104_1711 = goal in
               let uu____1712 =
                 let uu____1713 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1713 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___104_1711.witness);
                 goal_ty = uu____1712
               }
             else
               (let uu___105_1715 = goal in
                let uu____1716 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___105_1715.witness);
                  goal_ty = uu____1716
                }) in
           bind dismiss (fun uu____1717  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1724 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1724 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1736 =
                 let uu____1737 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1738 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1737 uu____1738 in
               fail uu____1736
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1751 = revert_all_hd xs1 in
        bind uu____1751 (fun uu____1753  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1757 =
      let uu____1758 = FStar_Syntax_Subst.compress x in
      uu____1758.FStar_Syntax_Syntax.n in
    match uu____1757 with
    | FStar_Syntax_Syntax.Tm_name uu____1761 -> true
    | uu____1762 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1766 =
      let uu____1767 = FStar_Syntax_Subst.compress x in
      uu____1767.FStar_Syntax_Syntax.n in
    match uu____1766 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1771 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun t  ->
    let uu____1783 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1783 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____1795)::(rhs,uu____1797)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____1823 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____1823 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____1895 =
               let uu____1903 = as_name x in (uu____1903, e, rhs) in
             Some uu____1895
         | uu____1915 -> None)
    | uu____1924 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____1947 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____1956 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____1956
           then
             let uu____1958 =
               let uu___106_1959 = p in
               let uu____1960 =
                 let uu____1962 = conj_goals g1 g2 in uu____1962 :: rest in
               {
                 main_context = (uu___106_1959.main_context);
                 main_goal = (uu___106_1959.main_goal);
                 all_implicits = (uu___106_1959.all_implicits);
                 goals = uu____1960;
                 smt_goals = (uu___106_1959.smt_goals);
                 transaction = (uu___106_1959.transaction)
               } in
             set uu____1958
           else
             (let g1_binders =
                let uu____1965 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____1965
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____1967 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____1967
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____1968 =
                let uu____1969 = goal_to_string g1 in
                let uu____1970 = goal_to_string g2 in
                let uu____1971 =
                  let uu____1972 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____1972 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____1969 uu____1970 uu____1971 in
              fail uu____1968)
       | uu____1973 ->
           let goals =
             let uu____1976 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____1976 (FStar_String.concat "\n\t") in
           let uu____1982 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____1982)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___107_1992 = g in
           {
             context = ctx';
             witness = (uu___107_1992.witness);
             goal_ty = (uu___107_1992.goal_ty)
           } in
         bind dismiss (fun uu____1993  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___108_2003 = g in
           {
             context = ctx';
             witness = (uu___108_2003.witness);
             goal_ty = (uu___108_2003.goal_ty)
           } in
         bind dismiss (fun uu____2004  -> add_goals [g']))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2008 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2012 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2016 -> false
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
        let uu____2033 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2033 } in
      let uu____2034 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2034
      }