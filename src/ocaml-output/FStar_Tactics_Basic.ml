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
       | [] -> fail "No more goals"
       | uu____681::[] -> bind f (fun a  -> ret (a, None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____696  ->
                let uu____697 = add_goals [hd1] in
                bind uu____697
                  (fun uu____702  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____710  ->
                               match uu____710 with
                               | { main_context = uu____715;
                                   main_goal = uu____716;
                                   all_implicits = uu____717;
                                   goals = sub_goals_f;
                                   smt_goals = uu____719;
                                   transaction = uu____720;_} ->
                                   bind dismiss_all
                                     (fun uu____726  ->
                                        let uu____727 = add_goals tl1 in
                                        bind uu____727
                                          (fun uu____732  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____737 =
                                                    add_goals sub_goals_f in
                                                  bind uu____737
                                                    (fun uu____742  ->
                                                       ret (a, (Some b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____765 = t1.tac_f p in
       match uu____765 with | Failed uu____768 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____786 =
         let uu____789 =
           let uu____795 = map t in cur_goal_and_rest t uu____795 in
         bind uu____789
           (fun uu___81_804  ->
              match uu___81_804 with
              | (hd1,None ) -> ret [hd1]
              | (hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____786 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal
        (fun g  ->
           let uu____837 =
             let uu___92_838 = g in
             let uu____839 = f g.goal_ty in
             {
               context = (uu___92_838.context);
               witness = (uu___92_838.witness);
               goal_ty = uu____839
             } in
           replace_cur uu____837) in
    let uu____840 = map aux in bind uu____840 (fun uu____844  -> ret ())
let map_meta t =
  with_cur_goal
    (fun g  ->
       let uu____857 =
         let uu____858 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____858.FStar_Syntax_Syntax.n in
       match uu____857 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____868 =
             replace_cur
               (let uu___93_870 = g in
                {
                  context = (uu___93_870.context);
                  witness = (uu___93_870.witness);
                  goal_ty = f
                }) in
           bind uu____868
             (fun uu____871  ->
                bind t
                  (fun a  ->
                     let uu____873 =
                       map_goal_term
                         (fun tm  ->
                            let uu____876 = is_true tm in
                            if uu____876
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____873 (fun uu____882  -> ret a)))
       | uu____883 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____896 =
        bind t1
          (fun uu____898  ->
             let uu____899 = map t2 in
             bind uu____899 (fun uu____903  -> ret ())) in
      focus_cur_goal uu____896
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal
    (fun goal  ->
       let uu____907 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____907 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____915  ->
                let uu____916 = add_goals [new_goal] in
                bind uu____916
                  (fun uu____918  ->
                     let uu____919 =
                       FStar_All.pipe_left mlog
                         (fun uu____924  ->
                            let uu____925 =
                              FStar_Syntax_Print.binders_to_string ", " bs in
                            FStar_Util.print1 "intros: %s\n" uu____925) in
                     bind uu____919 (fun uu____926  -> ret bs)))
       | uu____927 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____930  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____941 = let uu____947 = FStar_Syntax_Syntax.as_arg p in [uu____947] in
  FStar_Syntax_Util.mk_app sq uu____941
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____954 = FStar_Syntax_Util.head_and_args t in
    match uu____954 with
    | (head1,args) ->
        let uu____983 =
          let uu____991 =
            let uu____992 = FStar_Syntax_Util.un_uinst head1 in
            uu____992.FStar_Syntax_Syntax.n in
          (uu____991, args) in
        (match uu____983 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____1005)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1025;
               FStar_Syntax_Syntax.index = uu____1026;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1028;
                   FStar_Syntax_Syntax.pos = uu____1029;
                   FStar_Syntax_Syntax.vars = uu____1030;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____1049 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal
    (fun goal  ->
       let uu____1061 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1061 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1066)::(rhs,uu____1068)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1096 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1096; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1097  ->
                let uu____1098 = add_goals [new_goal] in
                bind uu____1098
                  (fun uu____1100  ->
                     let uu____1101 =
                       FStar_All.pipe_left mlog
                         (fun uu____1106  ->
                            let uu____1107 =
                              FStar_Syntax_Print.bv_to_string name in
                            FStar_Util.print1 "imp_intro: %s\n" uu____1107) in
                     bind uu____1101
                       (fun uu____1108  ->
                          let uu____1109 = FStar_Syntax_Syntax.mk_binder name in
                          ret uu____1109)))
       | uu____1110 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1114 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1114 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1124  ->
                     match uu____1124 with
                     | (a,uu____1128) ->
                         let uu___94_1129 = goal in
                         {
                           context = (uu___94_1129.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1130  -> add_goals new_goals)
       | uu____1131 -> fail "Cannot split this goal; expected a conjunction")
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
       let uu____1138 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1138 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid ->
           bind dismiss
             (fun uu____1151  ->
                add_goals
                  [(let uu___95_1152 = goal in
                    {
                      context = (uu___95_1152.context);
                      witness = (uu___95_1152.witness);
                      goal_ty = t
                    })])
       | uu____1153 -> fail "Not a trivial goal")
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1164 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1164 with
           | (tm1,t,guard) ->
               let uu____1172 =
                 let uu____1173 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1173 in
               if uu____1172
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1176 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1176 with
                  | (bs,comp) ->
                      let uu____1191 =
                        FStar_List.fold_left
                          (fun uu____1208  ->
                             fun uu____1209  ->
                               match (uu____1208, uu____1209) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1258 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1258 with
                                    | (u,uu____1273,g_u) ->
                                        let uu____1281 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1281,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1191 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1313 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1329 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1359 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1313 with
                            | (pre,post) ->
                                let uu____1382 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1382 with
                                 | None  ->
                                     fail
                                       "apply_lemma: does not unify with goal"
                                 | Some g ->
                                     let g1 =
                                       let uu____1387 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1387
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1423  ->
                                               match uu____1423 with
                                               | (uu____1430,uu____1431,uu____1432,tm2,uu____1434,uu____1435)
                                                   ->
                                                   let uu____1436 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1436 with
                                                    | (hd1,uu____1447) ->
                                                        let uu____1462 =
                                                          let uu____1463 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1463.FStar_Syntax_Syntax.n in
                                                        (match uu____1462
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1466 ->
                                                             true
                                                         | uu____1475 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____1479 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____1495  ->
                                                   match uu____1495 with
                                                   | (_msg,_env,_uvar,term,typ,uu____1507)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (Some term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___98_1508 = goal in
                                          {
                                            context = (uu___98_1508.context);
                                            witness = None;
                                            goal_ty = pre
                                          }) :: uu____1479 in
                                       let uu____1509 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1509
                                         (fun uu____1511  ->
                                            bind dismiss
                                              (fun uu____1512  ->
                                                 add_goals sub_goals))))))))
         with | uu____1515 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1525 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1525 with
           | (uu____1530,t,guard) ->
               let uu____1533 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1533
               then
                 (solve goal tm;
                  replace_cur
                    (let uu___101_1536 = goal in
                     {
                       context = (uu___101_1536.context);
                       witness = None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____1539 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1540 = FStar_Syntax_Print.term_to_string t in
                    let uu____1541 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1539
                      uu____1540 uu____1541 in
                  fail msg)
         with
         | e ->
             let uu____1545 =
               let uu____1546 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1546 in
             fail uu____1545)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal
      (fun goal  ->
         let uu____1553 =
           FStar_All.pipe_left mlog
             (fun uu____1558  ->
                let uu____1559 =
                  FStar_Syntax_Print.bv_to_string (Prims.fst h) in
                let uu____1560 =
                  FStar_Syntax_Print.term_to_string
                    (Prims.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1559
                  uu____1560) in
         bind uu____1553
           (fun uu____1561  ->
              let uu____1562 =
                let uu____1564 =
                  let uu____1565 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (Prims.fst h) in
                  FStar_All.pipe_left Prims.fst uu____1565 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1564 in
              match uu____1562 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1572::(x,uu____1574)::(e,uu____1576)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____1610 =
                    let uu____1611 = FStar_Syntax_Subst.compress x in
                    uu____1611.FStar_Syntax_Syntax.n in
                  (match uu____1610 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___102_1617 = goal in
                         let uu____1618 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___102_1617.context);
                           witness = (uu___102_1617.witness);
                           goal_ty = uu____1618
                         } in
                       replace_cur goal1
                   | uu____1621 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____1622 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1626 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1626 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1639 = FStar_Util.set_mem x fns in
           if uu____1639
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___103_1643 = goal in
                {
                  context = env';
                  witness = (uu___103_1643.witness);
                  goal_ty = (uu___103_1643.goal_ty)
                } in
              bind dismiss (fun uu____1644  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1651 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1651 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1666 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1666 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1680 = FStar_Util.set_mem x fvs in
             if uu____1680
             then
               let uu___104_1681 = goal in
               let uu____1682 =
                 let uu____1683 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1683 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___104_1681.witness);
                 goal_ty = uu____1682
               }
             else
               (let uu___105_1685 = goal in
                let uu____1686 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___105_1685.witness);
                  goal_ty = uu____1686
                }) in
           bind dismiss (fun uu____1687  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1694 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1694 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1706 =
                 let uu____1707 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1708 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1707 uu____1708 in
               fail uu____1706
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1721 = revert_all_hd xs1 in
        bind uu____1721 (fun uu____1723  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1727 =
      let uu____1728 = FStar_Syntax_Subst.compress x in
      uu____1728.FStar_Syntax_Syntax.n in
    match uu____1727 with
    | FStar_Syntax_Syntax.Tm_name uu____1731 -> true
    | uu____1732 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1736 =
      let uu____1737 = FStar_Syntax_Subst.compress x in
      uu____1737.FStar_Syntax_Syntax.n in
    match uu____1736 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1741 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun t  ->
    let uu____1753 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1753 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____1765)::(rhs,uu____1767)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____1793 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____1793 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____1865 =
               let uu____1873 = as_name x in (uu____1873, e, rhs) in
             Some uu____1865
         | uu____1885 -> None)
    | uu____1894 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____1917 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____1926 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____1926
           then
             let uu____1928 =
               let uu___106_1929 = p in
               let uu____1930 =
                 let uu____1932 = conj_goals g1 g2 in uu____1932 :: rest in
               {
                 main_context = (uu___106_1929.main_context);
                 main_goal = (uu___106_1929.main_goal);
                 all_implicits = (uu___106_1929.all_implicits);
                 goals = uu____1930;
                 smt_goals = (uu___106_1929.smt_goals);
                 transaction = (uu___106_1929.transaction)
               } in
             set uu____1928
           else
             (let g1_binders =
                let uu____1935 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____1935
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____1937 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____1937
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____1938 =
                let uu____1939 = goal_to_string g1 in
                let uu____1940 = goal_to_string g2 in
                let uu____1941 =
                  let uu____1942 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____1942 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____1939 uu____1940 uu____1941 in
              fail uu____1938)
       | uu____1943 ->
           let goals =
             let uu____1946 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____1946 (FStar_String.concat "\n\t") in
           let uu____1952 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____1952)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___107_1962 = g in
           {
             context = ctx';
             witness = (uu___107_1962.witness);
             goal_ty = (uu___107_1962.goal_ty)
           } in
         bind dismiss (fun uu____1963  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___108_1973 = g in
           {
             context = ctx';
             witness = (uu___108_1973.witness);
             goal_ty = (uu___108_1973.goal_ty)
           } in
         bind dismiss (fun uu____1974  -> add_goals [g']))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____1978 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____1982 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____1986 -> false
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
        let uu____2003 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2003 } in
      let uu____2004 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2004
      }