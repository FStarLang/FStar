open Prims
type name = FStar_Syntax_Syntax.bv
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
type 'a tac = {
  tac_f: proofstate -> 'a result;}
let mk_tac f = { tac_f = f }
let run t p = t.tac_f p
let ret x = mk_tac (fun p  -> Success (x, p))
let bind t1 t2 =
  mk_tac
    (fun p  ->
       let uu____256 = run t1 p in
       match uu____256 with
       | Success (a,q) -> let uu____261 = t2 a in run uu____261 q
       | Failed (msg,q) -> Failed (msg, q))
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____269 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____269
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____270 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format2 "%s |- %s" g_binders uu____270
let dump_goal: goal -> Prims.unit =
  fun goal  ->
    let uu____275 = goal_to_string goal in
    FStar_Util.print1 "TAC>> %s\n" uu____275
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun p  ->
    fun msg  ->
      FStar_Util.print1 "TAC>> State dump (%s):\n" msg;
      (let uu____284 = FStar_Util.string_of_int (FStar_List.length p.goals) in
       FStar_Util.print1 "TAC>> ACTIVE goals (%s):\n" uu____284);
      FStar_List.iter dump_goal p.goals;
      (let uu____290 =
         FStar_Util.string_of_int (FStar_List.length p.smt_goals) in
       FStar_Util.print1 "TAC>> SMT goals (%s):\n" uu____290);
      FStar_List.iter dump_goal p.smt_goals
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let fail msg = mk_tac (fun p  -> Failed (msg, p))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____318  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      match goal.witness with
      | None  -> ()
      | Some w ->
          let uu____326 =
            FStar_TypeChecker_Rel.teq_nosmt goal.context w solution in
          if uu____326
          then ()
          else
            (let uu____328 =
               let uu____329 =
                 let uu____330 = FStar_Syntax_Print.term_to_string solution in
                 let uu____331 = FStar_Syntax_Print.term_to_string w in
                 let uu____332 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 FStar_Util.format3 "%s does not solve %s : %s" uu____330
                   uu____331 uu____332 in
               Failure uu____329 in
             Prims.raise uu____328)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____335 =
         let uu___82_336 = p in
         let uu____337 = FStar_List.tl p.goals in
         {
           main_context = (uu___82_336.main_context);
           main_goal = (uu___82_336.main_goal);
           all_implicits = (uu___82_336.all_implicits);
           goals = uu____337;
           smt_goals = (uu___82_336.smt_goals);
           transaction = (uu___82_336.transaction)
         } in
       set uu____335)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___83_341 = p in
          {
            main_context = (uu___83_341.main_context);
            main_goal = (uu___83_341.main_goal);
            all_implicits = (uu___83_341.all_implicits);
            goals = [];
            smt_goals = (uu___83_341.smt_goals);
            transaction = (uu___83_341.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_350 = p in
            {
              main_context = (uu___84_350.main_context);
              main_goal = (uu___84_350.main_goal);
              all_implicits = (uu___84_350.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___84_350.smt_goals);
              transaction = (uu___84_350.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___85_359 = p in
            {
              main_context = (uu___85_359.main_context);
              main_goal = (uu___85_359.main_goal);
              all_implicits = (uu___85_359.all_implicits);
              goals = (uu___85_359.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___85_359.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____365  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___86_372 = p in
            {
              main_context = (uu___86_372.main_context);
              main_goal = (uu___86_372.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___86_372.goals);
              smt_goals = (uu___86_372.smt_goals);
              transaction = (uu___86_372.transaction)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____382 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____382 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid
    | uu____394 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____399 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____399 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid
    | uu____411 -> false
let conj_goals: goal -> goal -> goal =
  fun g1  ->
    fun g2  ->
      let t1 = g1.goal_ty in
      let t2 = g2.goal_ty in
      let uu____421 = (is_true t1) || (is_false t2) in
      if uu____421
      then g2
      else
        (let uu____423 = (is_true t2) || (is_false t1) in
         if uu____423
         then g1
         else
           (let uu___87_425 = g1 in
            let uu____426 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___87_425.context);
              witness = (uu___87_425.witness);
              goal_ty = uu____426
            }))
let with_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with | [] -> fail "No more goals" | hd1::tl1 -> f hd1)
let cur_goal: goal tac =
  mk_tac
    (fun ps  ->
       match ps.goals with
       | hd1::uu____456 -> Success (hd1, ps)
       | uu____458 -> Failed ("No goals left", ps))
let set_cur_goal: goal -> Prims.unit tac =
  fun g  ->
    mk_tac
      (fun ps  ->
         match ps.goals with
         | hd1::tl1 ->
             Success
               ((),
                 (let uu___88_470 = ps in
                  {
                    main_context = (uu___88_470.main_context);
                    main_goal = (uu___88_470.main_goal);
                    all_implicits = (uu___88_470.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___88_470.smt_goals);
                    transaction = (uu___88_470.transaction)
                  }))
         | uu____471 -> Failed ("No goals left", ps))
let replace_point:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun e1  ->
    fun e2  ->
      fun t  ->
        let uu____482 = FStar_Syntax_Util.term_eq e1 t in
        if uu____482 then e2 else t
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
                 let uu____523 = FStar_TypeChecker_Rel.try_teq true env t1 t2 in
                 match uu____523 with
                 | None  -> false
                 | Some g1 -> FStar_TypeChecker_Rel.is_trivial g1 in
               if ok
               then
                 let goal_ty' = treplace env e1 e2 g.goal_ty in
                 let uu____528 =
                   set_cur_goal
                     (let uu___89_530 = g in
                      {
                        context = (uu___89_530.context);
                        witness = (uu___89_530.witness);
                        goal_ty = goal_ty'
                      }) in
                 bind uu____528
                   (fun uu____531  ->
                      let uu____532 =
                        let uu____534 =
                          let uu____535 =
                            FStar_Syntax_Util.mk_eq2
                              FStar_Syntax_Syntax.U_zero t1 e1 e2 in
                          {
                            context = (g.context);
                            witness = None;
                            goal_ty = uu____535
                          } in
                        [uu____534] in
                      add_goals uu____532)
               else
                 (FStar_TypeChecker_Err.add_errors env
                    [("Ill-type rewriting requested",
                       (e1.FStar_Syntax_Syntax.pos))];
                  fail "grewrite: Ill-typed rewriting requested"))
let smt: Prims.unit tac =
  with_cur_goal "smt"
    (fun g  ->
       bind dismiss
         (fun uu____544  ->
            let uu____545 =
              add_goals
                [(let uu___90_547 = g in
                  {
                    context = (uu___90_547.context);
                    witness = (uu___90_547.witness);
                    goal_ty = FStar_Syntax_Util.t_true
                  })] in
            bind uu____545 (fun uu____548  -> add_smt_goals [g])))
let focus_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___91_570 = p in
             {
               main_context = (uu___91_570.main_context);
               main_goal = (uu___91_570.main_goal);
               all_implicits = (uu___91_570.all_implicits);
               goals = [hd1];
               smt_goals = (uu___91_570.smt_goals);
               transaction = (uu___91_570.transaction)
             } in
           let uu____571 = set q in
           bind uu____571
             (fun uu____573  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___92_577 = q' in
                            {
                              main_context = (uu___92_577.main_context);
                              main_goal = (uu___92_577.main_goal);
                              all_implicits = (uu___92_577.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___92_577.smt_goals);
                              transaction = (uu___92_577.transaction)
                            } in
                          let uu____578 = set q2 in
                          bind uu____578 (fun uu____580  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | uu____614::[] -> bind f (fun a  -> ret (a, None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____629  ->
                let uu____630 = add_goals [hd1] in
                bind uu____630
                  (fun uu____635  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____643  ->
                               match uu____643 with
                               | { main_context = uu____648;
                                   main_goal = uu____649;
                                   all_implicits = uu____650;
                                   goals = sub_goals_f;
                                   smt_goals = uu____652;
                                   transaction = uu____653;_} ->
                                   bind dismiss_all
                                     (fun uu____659  ->
                                        let uu____660 = add_goals tl1 in
                                        bind uu____660
                                          (fun uu____665  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____670 =
                                                    add_goals sub_goals_f in
                                                  bind uu____670
                                                    (fun uu____675  ->
                                                       ret (a, (Some b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____698 = t1.tac_f p in
       match uu____698 with | Failed uu____701 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____719 =
         let uu____722 =
           let uu____728 = map t in cur_goal_and_rest t uu____728 in
         bind uu____722
           (fun uu___81_737  ->
              match uu___81_737 with
              | (hd1,None ) -> ret [hd1]
              | (hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____719 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal "map_goal"
        (fun g  ->
           let uu____770 =
             let uu___93_771 = g in
             let uu____772 = f g.goal_ty in
             {
               context = (uu___93_771.context);
               witness = (uu___93_771.witness);
               goal_ty = uu____772
             } in
           replace_cur uu____770) in
    let uu____773 = map aux in bind uu____773 (fun uu____777  -> ret ())
let map_meta t =
  with_cur_goal "map_meta"
    (fun g  ->
       let uu____790 =
         let uu____791 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____791.FStar_Syntax_Syntax.n in
       match uu____790 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____801 =
             replace_cur
               (let uu___94_803 = g in
                {
                  context = (uu___94_803.context);
                  witness = (uu___94_803.witness);
                  goal_ty = f
                }) in
           bind uu____801
             (fun uu____804  ->
                bind t
                  (fun a  ->
                     let uu____806 =
                       map_goal_term
                         (fun tm  ->
                            let uu____809 = is_true tm in
                            if uu____809
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____806 (fun uu____815  -> ret a)))
       | uu____816 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____829 =
        bind t1
          (fun uu____831  ->
             let uu____832 = map t2 in
             bind uu____832 (fun uu____836  -> ret ())) in
      focus_cur_goal "seq" uu____829
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal "intros"
    (fun goal  ->
       let uu____840 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____840 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____848  ->
                let uu____849 = add_goals [new_goal] in
                bind uu____849
                  (fun uu____851  ->
                     (let uu____853 =
                        FStar_Syntax_Print.binders_to_string ", " bs in
                      FStar_Util.print1 "intros: %s\n" uu____853);
                     ret bs))
       | uu____854 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____857  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____868 = let uu____874 = FStar_Syntax_Syntax.as_arg p in [uu____874] in
  FStar_Syntax_Util.mk_app sq uu____868
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____881 = FStar_Syntax_Util.head_and_args t in
    match uu____881 with
    | (head1,args) ->
        let uu____910 =
          let uu____918 =
            let uu____919 = FStar_Syntax_Util.un_uinst head1 in
            uu____919.FStar_Syntax_Syntax.n in
          (uu____918, args) in
        (match uu____910 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____932)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____952;
               FStar_Syntax_Syntax.index = uu____953;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____955;
                   FStar_Syntax_Syntax.pos = uu____956;
                   FStar_Syntax_Syntax.vars = uu____957;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____976 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal "imp_intro"
    (fun goal  ->
       let uu____988 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____988 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____993)::(rhs,uu____995)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1023 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1023; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1024  ->
                let uu____1025 = add_goals [new_goal] in
                bind uu____1025
                  (fun uu____1027  ->
                     (let uu____1029 = FStar_Syntax_Print.bv_to_string name in
                      FStar_Util.print1 "imp_intro: %s\n" uu____1029);
                     (let uu____1030 = FStar_Syntax_Syntax.mk_binder name in
                      ret uu____1030)))
       | uu____1031 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal "split"
    (fun goal  ->
       let uu____1035 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1035 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1045  ->
                     match uu____1045 with
                     | (a,uu____1049) ->
                         let uu___95_1050 = goal in
                         {
                           context = (uu___95_1050.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1051  -> add_goals new_goals)
       | uu____1052 -> fail "Cannot split this goal; expected a conjunction")
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
       let uu____1059 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1059 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid ->
           bind dismiss
             (fun uu____1072  ->
                add_goals
                  [(let uu___96_1073 = goal in
                    {
                      context = (uu___96_1073.context);
                      witness = (uu___96_1073.witness);
                      goal_ty = t
                    })])
       | uu____1074 ->
           let uu____1076 = print_proof_state "`trivial` is failing" in
           bind uu____1076 (fun uu____1078  -> fail "Not a trivial goal"))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "apply_lemma"
      (fun goal  ->
         try
           let uu____1088 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1088 with
           | (tm1,t,guard) ->
               let uu____1096 =
                 let uu____1097 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1097 in
               if uu____1096
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1100 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1100 with
                  | (bs,comp) ->
                      let uu____1115 =
                        FStar_List.fold_left
                          (fun uu____1132  ->
                             fun uu____1133  ->
                               match (uu____1132, uu____1133) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1182 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1182 with
                                    | (u,uu____1197,g_u) ->
                                        let uu____1205 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1205,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1115 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1237 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1253 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1283 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1237 with
                            | (pre,post) ->
                                let uu____1306 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1306 with
                                 | None  ->
                                     fail
                                       "apply_lemma: does not unify with goal"
                                 | Some g ->
                                     let g1 =
                                       let uu____1311 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1311
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1347  ->
                                               match uu____1347 with
                                               | (uu____1354,uu____1355,uu____1356,tm2,uu____1358,uu____1359)
                                                   ->
                                                   let uu____1360 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1360 with
                                                    | (hd1,uu____1371) ->
                                                        let uu____1386 =
                                                          let uu____1387 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1387.FStar_Syntax_Syntax.n in
                                                        (match uu____1386
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1390 ->
                                                             true
                                                         | uu____1399 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____1403 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____1419  ->
                                                   match uu____1419 with
                                                   | (_msg,_env,_uvar,term,typ,uu____1431)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (Some term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___99_1432 = goal in
                                          {
                                            context = (uu___99_1432.context);
                                            witness = None;
                                            goal_ty = pre
                                          }) :: uu____1403 in
                                       let uu____1433 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1433
                                         (fun uu____1435  ->
                                            bind dismiss
                                              (fun uu____1436  ->
                                                 add_goals sub_goals))))))))
         with | uu____1439 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "exact"
      (fun goal  ->
         try
           let uu____1449 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1449 with
           | (uu____1454,t,guard) ->
               let uu____1457 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1457
               then
                 (solve goal tm;
                  replace_cur
                    (let uu___102_1460 = goal in
                     {
                       context = (uu___102_1460.context);
                       witness = None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____1463 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1464 = FStar_Syntax_Print.term_to_string t in
                    let uu____1465 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1463
                      uu____1464 uu____1465 in
                  fail msg)
         with
         | e ->
             let uu____1469 =
               let uu____1470 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1470 in
             fail uu____1469)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal "rewrite"
      (fun goal  ->
         (let uu____1478 = FStar_Syntax_Print.bv_to_string (Prims.fst h) in
          let uu____1479 =
            FStar_Syntax_Print.term_to_string
              (Prims.fst h).FStar_Syntax_Syntax.sort in
          FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1478 uu____1479);
         (let uu____1480 =
            let uu____1482 =
              let uu____1483 =
                FStar_TypeChecker_Env.lookup_bv goal.context (Prims.fst h) in
              FStar_All.pipe_left Prims.fst uu____1483 in
            FStar_Syntax_Util.destruct_typ_as_formula uu____1482 in
          match uu____1480 with
          | Some (FStar_Syntax_Util.BaseConn
              (l,uu____1490::(x,uu____1492)::(e,uu____1494)::[])) when
              FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
              let uu____1528 =
                let uu____1529 = FStar_Syntax_Subst.compress x in
                uu____1529.FStar_Syntax_Syntax.n in
              (match uu____1528 with
               | FStar_Syntax_Syntax.Tm_name x1 ->
                   let goal1 =
                     let uu___103_1535 = goal in
                     let uu____1536 =
                       FStar_Syntax_Subst.subst
                         [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                     {
                       context = (uu___103_1535.context);
                       witness = (uu___103_1535.witness);
                       goal_ty = uu____1536
                     } in
                   replace_cur goal1
               | uu____1539 ->
                   fail
                     "Not an equality hypothesis with a variable on the LHS")
          | uu____1540 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal "clear"
    (fun goal  ->
       let uu____1544 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1544 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1557 = FStar_Util.set_mem x fns in
           if uu____1557
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___104_1561 = goal in
                {
                  context = env';
                  witness = (uu___104_1561.witness);
                  goal_ty = (uu___104_1561.goal_ty)
                } in
              bind dismiss (fun uu____1562  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "clear_hd"
      (fun goal  ->
         let uu____1569 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1569 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal "revert"
    (fun goal  ->
       let uu____1584 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1584 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1598 = FStar_Util.set_mem x fvs in
             if uu____1598
             then
               let uu___105_1599 = goal in
               let uu____1600 =
                 let uu____1601 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1601 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___105_1599.witness);
                 goal_ty = uu____1600
               }
             else
               (let uu___106_1603 = goal in
                let uu____1604 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___106_1603.witness);
                  goal_ty = uu____1604
                }) in
           bind dismiss (fun uu____1605  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "revert_hd"
      (fun goal  ->
         let uu____1612 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1612 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1624 =
                 let uu____1625 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1626 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1625 uu____1626 in
               fail uu____1624
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1639 = revert_all_hd xs1 in
        bind uu____1639 (fun uu____1641  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1645 =
      let uu____1646 = FStar_Syntax_Subst.compress x in
      uu____1646.FStar_Syntax_Syntax.n in
    match uu____1645 with
    | FStar_Syntax_Syntax.Tm_name uu____1649 -> true
    | uu____1650 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1654 =
      let uu____1655 = FStar_Syntax_Subst.compress x in
      uu____1655.FStar_Syntax_Syntax.n in
    match uu____1654 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1659 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun t  ->
    let uu____1671 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1671 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____1683)::(rhs,uu____1685)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____1711 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____1711 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____1783 =
               let uu____1791 = as_name x in (uu____1791, e, rhs) in
             Some uu____1783
         | uu____1803 -> None)
    | uu____1812 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____1835 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____1844 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____1844
           then
             let uu____1846 =
               let uu___107_1847 = p in
               let uu____1848 =
                 let uu____1850 = conj_goals g1 g2 in uu____1850 :: rest in
               {
                 main_context = (uu___107_1847.main_context);
                 main_goal = (uu___107_1847.main_goal);
                 all_implicits = (uu___107_1847.all_implicits);
                 goals = uu____1848;
                 smt_goals = (uu___107_1847.smt_goals);
                 transaction = (uu___107_1847.transaction)
               } in
             set uu____1846
           else
             (let g1_binders =
                let uu____1853 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____1853
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____1855 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____1855
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____1856 =
                let uu____1857 = goal_to_string g1 in
                let uu____1858 = goal_to_string g2 in
                let uu____1859 =
                  let uu____1860 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____1860 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____1857 uu____1858 uu____1859 in
              fail uu____1856)
       | uu____1861 ->
           let goals =
             let uu____1864 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____1864 (FStar_String.concat "\n\t") in
           let uu____1870 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____1870)
let rec visit: Prims.unit tac -> Prims.unit tac =
  fun callback  ->
    let uu____1878 =
      let uu____1880 =
        with_cur_goal "visit_strengthen_else"
          (fun goal  ->
             let uu____1883 =
               FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
             match uu____1883 with
             | None  ->
                 let uu____1886 =
                   let uu____1887 = FStar_Syntax_Subst.compress goal.goal_ty in
                   uu____1887.FStar_Syntax_Syntax.n in
                 (match uu____1886 with
                  | FStar_Syntax_Syntax.Tm_meta uu____1891 ->
                      let uu____1896 = visit callback in map_meta uu____1896
                  | uu____1898 ->
                      ((let uu____1900 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        FStar_Util.print1 "Not a formula, split to smt %s\n"
                          uu____1900);
                       smt))
             | Some (FStar_Syntax_Util.QEx uu____1901) ->
                 ((let uu____1906 =
                     FStar_Syntax_Print.term_to_string goal.goal_ty in
                   FStar_Util.print1
                     "Not yet handled: exists\n\tGoal is %s\n" uu____1906);
                  ret ())
             | Some (FStar_Syntax_Util.QAll (xs,uu____1908,uu____1909)) ->
                 bind intros
                   (fun binders  ->
                      let uu____1911 = visit callback in
                      let uu____1913 =
                        let uu____1915 =
                          let uu____1917 = FStar_List.map Prims.fst binders in
                          revert_all_hd uu____1917 in
                        bind uu____1915
                          (fun uu____1921  ->
                             with_cur_goal "inner"
                               (fun goal1  ->
                                  (let uu____1924 = goal_to_string goal1 in
                                   FStar_Util.print1
                                     "After reverting intros, goal is %s\n"
                                     uu____1924);
                                  ret ())) in
                      seq uu____1911 uu____1913)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____1926)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
                 let uu____1927 =
                   let uu____1929 = visit callback in seq split uu____1929 in
                 bind uu____1927 (fun uu____1931  -> merge_sub_goals)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____1933)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
                 bind imp_intro
                   (fun h  ->
                      let uu____1935 = visit callback in
                      seq uu____1935 revert)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____1938)) ->
                 or_else trivial smt) in
      or_else callback uu____1880 in
    focus_cur_goal "visit_strengthen" uu____1878
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> proofstate =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____1946 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____1946 } in
      let uu____1947 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____1947
      }