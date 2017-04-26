open Prims
type name = FStar_Syntax_Syntax.bv
type em_term = FStar_Syntax_Syntax.term
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
  match projectee with | Success _0 -> true | uu____100 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success _0 -> _0
let uu___is_Failed projectee =
  match projectee with | Failed _0 -> true | uu____131 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed _0 -> _0
exception Failure of Prims.string
let uu___is_Failure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Failure uu____155 -> true | uu____156 -> false
let __proj__Failure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Failure uu____163 -> uu____163
type 'a tac =
  {
  tac_f: proofstate -> 'a result;
  tac_name: Prims.string;
  kernel: Prims.bool;}
let kernel_tac n1 t = { tac_f = t; tac_name = n1; kernel = true }
let user_tac n1 t = { tac_f = t; tac_name = n1; kernel = false }
let name_tac n1 t =
  let uu___77_275 = t in
  { tac_f = (uu___77_275.tac_f); tac_name = n1; kernel = false }
let run t p = t.tac_f p
let debug: proofstate -> Prims.string -> Prims.unit =
  fun p  ->
    fun msg  ->
      let uu____298 = FStar_Util.string_of_int (FStar_List.length p.goals) in
      let uu____302 =
        match p.goals with
        | [] -> "[]"
        | uu____303 ->
            let uu____305 =
              let uu____306 = FStar_List.hd p.goals in uu____306.goal_ty in
            FStar_Syntax_Print.term_to_string uu____305 in
      let uu____307 =
        match p.goals with
        | [] -> ""
        | uu____308 ->
            let uu____310 =
              let uu____312 = FStar_List.tl p.goals in
              FStar_All.pipe_right uu____312
                (FStar_List.map
                   (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
            FStar_All.pipe_right uu____310 (FStar_String.concat ";;") in
      FStar_Util.print4
        "TAC (ngoals=%s, maingoal=%s, rest=%s):\n\tTAC>> %s\n" uu____298
        uu____302 uu____307 msg
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  ->
    kernel_tac "print_proof_state"
      (fun p  -> let uu____324 = debug p msg; ((), p) in Success uu____324)
let ret a = kernel_tac "return" (fun p  -> Success (a, p))
let bind t1 t2 =
  kernel_tac "bind"
    (fun p  ->
       let uu____362 = t1.tac_f p in
       match uu____362 with
       | Success (a,q) -> let t21 = t2 a in t21.tac_f q
       | Failed (msg,q) -> Failed (msg, q))
let get: proofstate tac = kernel_tac "get" (fun p  -> Success (p, p))
let fail msg =
  kernel_tac "fail"
    (fun p  -> FStar_Util.print1 ">>>>>%s\n" msg; Failed (msg, p))
let set: proofstate -> Prims.unit tac =
  fun p  -> kernel_tac "set" (fun uu____388  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      match goal.witness with
      | None  -> ()
      | Some w ->
          let uu____396 =
            FStar_TypeChecker_Rel.teq_nosmt goal.context w solution in
          if uu____396
          then ()
          else
            (let uu____398 =
               let uu____399 =
                 let uu____400 = FStar_Syntax_Print.term_to_string solution in
                 let uu____401 = FStar_Syntax_Print.term_to_string w in
                 let uu____402 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 FStar_Util.format3 "%s does not solve %s : %s" uu____400
                   uu____401 uu____402 in
               Failure uu____399 in
             Prims.raise uu____398)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____405 =
         let uu___78_406 = p in
         let uu____407 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_406.main_context);
           main_goal = (uu___78_406.main_goal);
           all_implicits = (uu___78_406.all_implicits);
           goals = uu____407;
           smt_goals = (uu___78_406.smt_goals);
           transaction = (uu___78_406.transaction)
         } in
       set uu____405)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_411 = p in
          {
            main_context = (uu___79_411.main_context);
            main_goal = (uu___79_411.main_goal);
            all_implicits = (uu___79_411.all_implicits);
            goals = [];
            smt_goals = (uu___79_411.smt_goals);
            transaction = (uu___79_411.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_420 = p in
            {
              main_context = (uu___80_420.main_context);
              main_goal = (uu___80_420.main_goal);
              all_implicits = (uu___80_420.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_420.smt_goals);
              transaction = (uu___80_420.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_429 = p in
            {
              main_context = (uu___81_429.main_context);
              main_goal = (uu___81_429.main_goal);
              all_implicits = (uu___81_429.all_implicits);
              goals = (uu___81_429.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___81_429.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____435  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___82_442 = p in
            {
              main_context = (uu___82_442.main_context);
              main_goal = (uu___82_442.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___82_442.goals);
              smt_goals = (uu___82_442.smt_goals);
              transaction = (uu___82_442.transaction)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____452 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____452 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid
    | uu____464 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____469 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____469 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid
    | uu____481 -> false
let conj_goals: goal -> goal -> goal =
  fun g1  ->
    fun g2  ->
      let t1 = g1.goal_ty in
      let t2 = g2.goal_ty in
      let uu____491 = (is_true t1) || (is_false t2) in
      if uu____491
      then g2
      else
        (let uu____493 = (is_true t2) || (is_false t1) in
         if uu____493
         then g1
         else
           (let uu___83_495 = g1 in
            let uu____496 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___83_495.context);
              witness = (uu___83_495.witness);
              goal_ty = uu____496
            }))
let with_cur_goal nm f =
  let uu____517 =
    bind get
      (fun p  ->
         match p.goals with | [] -> fail "No more goals" | hd1::tl1 -> f hd1) in
  name_tac nm uu____517
let cur_goal: goal tac =
  kernel_tac "cur_goal"
    (fun ps  ->
       match ps.goals with
       | hd1::uu____528 -> Success (hd1, ps)
       | uu____530 -> Failed ("No goals left", ps))
let set_cur_goal: goal -> Prims.unit tac =
  fun g  ->
    kernel_tac "set_cur_goal"
      (fun ps  ->
         match ps.goals with
         | hd1::tl1 ->
             Success
               ((),
                 (let uu___84_542 = ps in
                  {
                    main_context = (uu___84_542.main_context);
                    main_goal = (uu___84_542.main_goal);
                    all_implicits = (uu___84_542.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___84_542.smt_goals);
                    transaction = (uu___84_542.transaction)
                  }))
         | uu____543 -> Failed ("No goals left", ps))
let replace_point:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun e1  ->
    fun e2  ->
      fun t  ->
        let uu____554 = FStar_Syntax_Util.term_eq e1 t in
        if uu____554 then e2 else t
let rec replace_in_term:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun e1  ->
    fun e2  ->
      fun t  -> FStar_Syntax_Util.bottom_fold (replace_point e1 e2) t
let treplace env e1 e2 t =
  (let uu____588 = FStar_Syntax_Print.term_to_string e1 in
   let uu____589 = FStar_Syntax_Print.term_to_string e2 in
   let uu____590 = FStar_Syntax_Print.term_to_string t in
   FStar_Util.print3 "TAC replacing %s for %s in %s\n" uu____588 uu____589
     uu____590);
  replace_in_term e1 e2 t
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
                 let uu____608 = FStar_TypeChecker_Rel.try_teq true env t1 t2 in
                 match uu____608 with
                 | None  -> false
                 | Some g1 -> FStar_TypeChecker_Rel.is_trivial g1 in
               if ok
               then
                 let goal_ty' = treplace env e1 e2 g.goal_ty in
                 let uu____613 =
                   set_cur_goal
                     (let uu___85_615 = g in
                      {
                        context = (uu___85_615.context);
                        witness = (uu___85_615.witness);
                        goal_ty = goal_ty'
                      }) in
                 bind uu____613
                   (fun uu____616  ->
                      let uu____617 =
                        let uu____619 =
                          let uu____620 =
                            FStar_Syntax_Util.mk_eq2
                              FStar_Syntax_Syntax.U_zero t1 e1 e2 in
                          {
                            context = (g.context);
                            witness = None;
                            goal_ty = uu____620
                          } in
                        [uu____619] in
                      add_goals uu____617)
               else
                 (FStar_TypeChecker_Err.add_errors env
                    [("Ill-type rewriting requested",
                       (e1.FStar_Syntax_Syntax.pos))];
                  fail "grewrite: Ill-typed rewriting requested"))
let smt: Prims.unit tac =
  with_cur_goal "smt"
    (fun g  ->
       bind dismiss
         (fun uu____629  ->
            let uu____630 =
              add_goals
                [(let uu___86_632 = g in
                  {
                    context = (uu___86_632.context);
                    witness = (uu___86_632.witness);
                    goal_ty = FStar_Syntax_Util.t_true
                  })] in
            bind uu____630 (fun uu____633  -> add_smt_goals [g])))
let focus_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___87_655 = p in
             {
               main_context = (uu___87_655.main_context);
               main_goal = (uu___87_655.main_goal);
               all_implicits = (uu___87_655.all_implicits);
               goals = [hd1];
               smt_goals = (uu___87_655.smt_goals);
               transaction = (uu___87_655.transaction)
             } in
           let uu____656 = set q in
           bind uu____656
             (fun uu____658  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___88_662 = q' in
                            {
                              main_context = (uu___88_662.main_context);
                              main_goal = (uu___88_662.main_goal);
                              all_implicits = (uu___88_662.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___88_662.smt_goals);
                              transaction = (uu___88_662.transaction)
                            } in
                          let uu____663 = set q2 in
                          bind uu____663 (fun uu____665  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | uu____699::[] -> bind f (fun a  -> ret (a, None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____714  ->
                let uu____715 = add_goals [hd1] in
                bind uu____715
                  (fun uu____720  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____728  ->
                               match uu____728 with
                               | { main_context = uu____733;
                                   main_goal = uu____734;
                                   all_implicits = uu____735;
                                   goals = sub_goals_f;
                                   smt_goals = uu____737;
                                   transaction = uu____738;_} ->
                                   bind dismiss_all
                                     (fun uu____744  ->
                                        let uu____745 = add_goals tl1 in
                                        bind uu____745
                                          (fun uu____750  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____755 =
                                                    add_goals sub_goals_f in
                                                  bind uu____755
                                                    (fun uu____760  ->
                                                       ret (a, (Some b)))))))))))
let or_else t1 t2 =
  kernel_tac "or_else"
    (fun p  ->
       let uu____783 = t1.tac_f p in
       match uu____783 with | Failed uu____786 -> t2.tac_f p | q -> q)
let rec map t =
  user_tac "map"
    (fun p  ->
       let uu____804 =
         let uu____807 =
           let uu____813 = map t in cur_goal_and_rest t uu____813 in
         bind uu____807
           (fun uu___76_822  ->
              match uu___76_822 with
              | (hd1,None ) -> ret [hd1]
              | (hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____804 p)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal "map_goal"
        (fun g  ->
           let uu____855 =
             let uu___89_856 = g in
             let uu____857 = f g.goal_ty in
             {
               context = (uu___89_856.context);
               witness = (uu___89_856.witness);
               goal_ty = uu____857
             } in
           replace_cur uu____855) in
    let uu____858 = map aux in bind uu____858 (fun uu____862  -> ret ())
let map_meta t =
  with_cur_goal "map_meta"
    (fun g  ->
       let uu____875 =
         let uu____876 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____876.FStar_Syntax_Syntax.n in
       match uu____875 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____886 =
             replace_cur
               (let uu___90_888 = g in
                {
                  context = (uu___90_888.context);
                  witness = (uu___90_888.witness);
                  goal_ty = f
                }) in
           bind uu____886
             (fun uu____889  ->
                bind t
                  (fun a  ->
                     let uu____891 =
                       map_goal_term
                         (fun tm  ->
                            let uu____894 = is_true tm in
                            if uu____894
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____891 (fun uu____900  -> ret a)))
       | uu____901 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____914 =
        bind t1
          (fun uu____916  ->
             let uu____917 = map t2 in
             bind uu____917 (fun uu____921  -> ret ())) in
      focus_cur_goal "seq" uu____914
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal "intros"
    (fun goal  ->
       let uu____925 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____925 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____933  ->
                let uu____934 = add_goals [new_goal] in
                bind uu____934
                  (fun uu____936  ->
                     (let uu____938 =
                        FStar_Syntax_Print.binders_to_string ", " bs in
                      FStar_Util.print1 "intros: %s\n" uu____938);
                     ret bs))
       | uu____939 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____942  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____953 = let uu____959 = FStar_Syntax_Syntax.as_arg p in [uu____959] in
  FStar_Syntax_Util.mk_app sq uu____953
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____966 = FStar_Syntax_Util.head_and_args t in
    match uu____966 with
    | (head1,args) ->
        let uu____995 =
          let uu____1003 =
            let uu____1004 = FStar_Syntax_Util.un_uinst head1 in
            uu____1004.FStar_Syntax_Syntax.n in
          (uu____1003, args) in
        (match uu____995 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____1017)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1037;
               FStar_Syntax_Syntax.index = uu____1038;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1040;
                   FStar_Syntax_Syntax.pos = uu____1041;
                   FStar_Syntax_Syntax.vars = uu____1042;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____1061 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal "imp_intro"
    (fun goal  ->
       let uu____1073 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1073 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1078)::(rhs,uu____1080)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1108 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1108; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1109  ->
                let uu____1110 = add_goals [new_goal] in
                bind uu____1110
                  (fun uu____1112  ->
                     (let uu____1114 = FStar_Syntax_Print.bv_to_string name in
                      FStar_Util.print1 "imp_intro: %s\n" uu____1114);
                     (let uu____1115 = FStar_Syntax_Syntax.mk_binder name in
                      ret uu____1115)))
       | uu____1116 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal "split"
    (fun goal  ->
       let uu____1120 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1120 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1130  ->
                     match uu____1130 with
                     | (a,uu____1134) ->
                         let uu___91_1135 = goal in
                         {
                           context = (uu___91_1135.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1136  -> add_goals new_goals)
       | uu____1137 -> fail "Cannot split this goal; expected a conjunction")
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
       let uu____1144 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1144 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid ->
           bind dismiss
             (fun uu____1157  ->
                add_goals
                  [(let uu___92_1158 = goal in
                    {
                      context = (uu___92_1158.context);
                      witness = (uu___92_1158.witness);
                      goal_ty = t
                    })])
       | uu____1159 -> fail "Not a trivial goal")
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "apply_lemma"
      (fun goal  ->
         try
           let uu____1170 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1170 with
           | (tm1,t,guard) ->
               let uu____1178 =
                 let uu____1179 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1179 in
               if uu____1178
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1182 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1182 with
                  | (bs,comp) ->
                      let uu____1197 =
                        FStar_List.fold_left
                          (fun uu____1214  ->
                             fun uu____1215  ->
                               match (uu____1214, uu____1215) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1264 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1264 with
                                    | (u,uu____1279,g_u) ->
                                        let uu____1287 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1287,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1197 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1319 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1335 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1365 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1319 with
                            | (pre,post) ->
                                let uu____1388 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1388 with
                                 | None  ->
                                     fail
                                       "apply_lemma: does not unify with goal"
                                 | Some g ->
                                     let g1 =
                                       let uu____1393 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1393
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1429  ->
                                               match uu____1429 with
                                               | (uu____1436,uu____1437,uu____1438,tm2,uu____1440,uu____1441)
                                                   ->
                                                   let uu____1442 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1442 with
                                                    | (hd1,uu____1453) ->
                                                        let uu____1468 =
                                                          let uu____1469 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1469.FStar_Syntax_Syntax.n in
                                                        (match uu____1468
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1472 ->
                                                             true
                                                         | uu____1481 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____1485 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____1501  ->
                                                   match uu____1501 with
                                                   | (_msg,_env,_uvar,term,typ,uu____1513)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (Some term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___95_1514 = goal in
                                          {
                                            context = (uu___95_1514.context);
                                            witness = None;
                                            goal_ty = pre
                                          }) :: uu____1485 in
                                       let uu____1515 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1515
                                         (fun uu____1517  ->
                                            bind dismiss
                                              (fun uu____1518  ->
                                                 add_goals sub_goals))))))))
         with | uu____1521 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "exact"
      (fun goal  ->
         try
           let uu____1531 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1531 with
           | (uu____1536,t,guard) ->
               let uu____1539 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1539
               then
                 (solve goal tm;
                  replace_cur
                    (let uu___98_1542 = goal in
                     {
                       context = (uu___98_1542.context);
                       witness = None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____1545 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1546 = FStar_Syntax_Print.term_to_string t in
                    let uu____1547 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1545
                      uu____1546 uu____1547 in
                  fail msg)
         with
         | e ->
             let uu____1551 =
               let uu____1552 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1552 in
             fail uu____1551)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal "rewrite"
      (fun goal  ->
         (let uu____1560 = FStar_Syntax_Print.bv_to_string (Prims.fst h) in
          let uu____1561 =
            FStar_Syntax_Print.term_to_string
              (Prims.fst h).FStar_Syntax_Syntax.sort in
          FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1560 uu____1561);
         (let uu____1562 =
            let uu____1564 =
              let uu____1565 =
                FStar_TypeChecker_Env.lookup_bv goal.context (Prims.fst h) in
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
                     let uu___99_1617 = goal in
                     let uu____1618 =
                       FStar_Syntax_Subst.subst
                         [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                     {
                       context = (uu___99_1617.context);
                       witness = (uu___99_1617.witness);
                       goal_ty = uu____1618
                     } in
                   replace_cur goal1
               | uu____1621 ->
                   fail
                     "Not an equality hypothesis with a variable on the LHS")
          | uu____1622 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal "clear"
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
                let uu___100_1643 = goal in
                {
                  context = env';
                  witness = (uu___100_1643.witness);
                  goal_ty = (uu___100_1643.goal_ty)
                } in
              bind dismiss (fun uu____1644  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "clear_hd"
      (fun goal  ->
         let uu____1651 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1651 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal "revert"
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
               let uu___101_1681 = goal in
               let uu____1682 =
                 let uu____1683 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1683 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___101_1681.witness);
                 goal_ty = uu____1682
               }
             else
               (let uu___102_1685 = goal in
                let uu____1686 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___102_1685.witness);
                  goal_ty = uu____1686
                }) in
           bind dismiss (fun uu____1687  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "revert_hd"
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
let goal_to_string: goal -> Prims.string =
  fun g1  ->
    let g1_binders =
      let uu____1923 = FStar_TypeChecker_Env.all_binders g1.context in
      FStar_All.pipe_right uu____1923
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____1924 = FStar_Syntax_Print.term_to_string g1.goal_ty in
    FStar_Util.format2 "%s |- %s" g1_binders uu____1924
let merge_sub_goals: Prims.unit tac =
  let uu____1926 =
    bind get
      (fun p  ->
         match p.goals with
         | g1::g2::rest ->
             let uu____1934 =
               ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                  (FStar_Option.isNone g1.witness))
                 && (FStar_Option.isNone g2.witness) in
             if uu____1934
             then
               let uu____1936 =
                 let uu___103_1937 = p in
                 let uu____1938 =
                   let uu____1940 = conj_goals g1 g2 in uu____1940 :: rest in
                 {
                   main_context = (uu___103_1937.main_context);
                   main_goal = (uu___103_1937.main_goal);
                   all_implicits = (uu___103_1937.all_implicits);
                   goals = uu____1938;
                   smt_goals = (uu___103_1937.smt_goals);
                   transaction = (uu___103_1937.transaction)
                 } in
               set uu____1936
             else
               (let g1_binders =
                  let uu____1943 =
                    FStar_TypeChecker_Env.all_binders g1.context in
                  FStar_All.pipe_right uu____1943
                    (FStar_Syntax_Print.binders_to_string ", ") in
                let g2_binders =
                  let uu____1945 =
                    FStar_TypeChecker_Env.all_binders g2.context in
                  FStar_All.pipe_right uu____1945
                    (FStar_Syntax_Print.binders_to_string ", ") in
                let uu____1946 =
                  let uu____1947 = goal_to_string g1 in
                  let uu____1948 = goal_to_string g2 in
                  let uu____1949 =
                    let uu____1950 =
                      FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                    FStar_All.pipe_right uu____1950 FStar_Util.string_of_bool in
                  FStar_Util.format3
                    "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                    uu____1947 uu____1948 uu____1949 in
                fail uu____1946)
         | uu____1951 ->
             let goals =
               let uu____1954 =
                 FStar_All.pipe_right p.goals
                   (FStar_List.map
                      (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
               FStar_All.pipe_right uu____1954 (FStar_String.concat "\n\t") in
             let uu____1960 =
               FStar_Util.format1
                 "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
                 goals in
             fail uu____1960) in
  name_tac "merge_sub_goals" uu____1926
let rec visit: Prims.unit tac -> Prims.unit tac =
  fun callback  ->
    let uu____1968 =
      let uu____1970 =
        with_cur_goal "visit_strengthen_else"
          (fun goal  ->
             let uu____1973 =
               FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
             match uu____1973 with
             | None  ->
                 let uu____1976 =
                   let uu____1977 = FStar_Syntax_Subst.compress goal.goal_ty in
                   uu____1977.FStar_Syntax_Syntax.n in
                 (match uu____1976 with
                  | FStar_Syntax_Syntax.Tm_meta uu____1981 ->
                      let uu____1986 = visit callback in map_meta uu____1986
                  | uu____1988 ->
                      ((let uu____1990 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        FStar_Util.print1 "Not a formula, split to smt %s\n"
                          uu____1990);
                       smt))
             | Some (FStar_Syntax_Util.QEx uu____1991) ->
                 ((let uu____1996 =
                     FStar_Syntax_Print.term_to_string goal.goal_ty in
                   FStar_Util.print1
                     "Not yet handled: exists\n\tGoal is %s\n" uu____1996);
                  ret ())
             | Some (FStar_Syntax_Util.QAll (xs,uu____1998,uu____1999)) ->
                 bind intros
                   (fun binders  ->
                      let uu____2001 = visit callback in
                      let uu____2003 =
                        let uu____2005 =
                          let uu____2007 = FStar_List.map Prims.fst binders in
                          revert_all_hd uu____2007 in
                        bind uu____2005
                          (fun uu____2011  ->
                             with_cur_goal "inner"
                               (fun goal1  ->
                                  (let uu____2014 = goal_to_string goal1 in
                                   FStar_Util.print1
                                     "After reverting intros, goal is %s\n"
                                     uu____2014);
                                  ret ())) in
                      seq uu____2001 uu____2003)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2016)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
                 let uu____2017 =
                   let uu____2019 = visit callback in seq split uu____2019 in
                 bind uu____2017 (fun uu____2021  -> merge_sub_goals)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2023)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
                 bind imp_intro
                   (fun h  ->
                      let uu____2025 = visit callback in
                      seq uu____2025 revert)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2028)) ->
                 or_else trivial smt) in
      or_else callback uu____1970 in
    focus_cur_goal "visit_strengthen" uu____1968
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> proofstate =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____2036 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2036 } in
      let uu____2037 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2037
      }