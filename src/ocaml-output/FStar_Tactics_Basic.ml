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
let dump_proofstate p msg =
  FStar_Util.print_string "TAC>> State dump:\n";
  (let uu____290 = FStar_Util.string_of_int (FStar_List.length p.goals) in
   FStar_Util.print1 "TAC>> ACTIVE goals (%s):\n" uu____290);
  FStar_List.iter dump_goal p.goals;
  (let uu____296 = FStar_Util.string_of_int (FStar_List.length p.smt_goals) in
   FStar_Util.print1 "TAC>> SMT goals (%s):\n" uu____296);
  FStar_List.iter dump_goal p.smt_goals
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let fail msg = mk_tac (fun p  -> Failed (msg, p))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____324  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      match goal.witness with
      | None  -> ()
      | Some w ->
          let uu____332 =
            FStar_TypeChecker_Rel.teq_nosmt goal.context w solution in
          if uu____332
          then ()
          else
            (let uu____334 =
               let uu____335 =
                 let uu____336 = FStar_Syntax_Print.term_to_string solution in
                 let uu____337 = FStar_Syntax_Print.term_to_string w in
                 let uu____338 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 FStar_Util.format3 "%s does not solve %s : %s" uu____336
                   uu____337 uu____338 in
               Failure uu____335 in
             Prims.raise uu____334)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____341 =
         let uu___82_342 = p in
         let uu____343 = FStar_List.tl p.goals in
         {
           main_context = (uu___82_342.main_context);
           main_goal = (uu___82_342.main_goal);
           all_implicits = (uu___82_342.all_implicits);
           goals = uu____343;
           smt_goals = (uu___82_342.smt_goals);
           transaction = (uu___82_342.transaction)
         } in
       set uu____341)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___83_347 = p in
          {
            main_context = (uu___83_347.main_context);
            main_goal = (uu___83_347.main_goal);
            all_implicits = (uu___83_347.all_implicits);
            goals = [];
            smt_goals = (uu___83_347.smt_goals);
            transaction = (uu___83_347.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_356 = p in
            {
              main_context = (uu___84_356.main_context);
              main_goal = (uu___84_356.main_goal);
              all_implicits = (uu___84_356.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___84_356.smt_goals);
              transaction = (uu___84_356.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___85_365 = p in
            {
              main_context = (uu___85_365.main_context);
              main_goal = (uu___85_365.main_goal);
              all_implicits = (uu___85_365.all_implicits);
              goals = (uu___85_365.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___85_365.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____371  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___86_378 = p in
            {
              main_context = (uu___86_378.main_context);
              main_goal = (uu___86_378.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___86_378.goals);
              smt_goals = (uu___86_378.smt_goals);
              transaction = (uu___86_378.transaction)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____388 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____388 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid
    | uu____400 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____405 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____405 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid
    | uu____417 -> false
let conj_goals: goal -> goal -> goal =
  fun g1  ->
    fun g2  ->
      let t1 = g1.goal_ty in
      let t2 = g2.goal_ty in
      let uu____427 = (is_true t1) || (is_false t2) in
      if uu____427
      then g2
      else
        (let uu____429 = (is_true t2) || (is_false t1) in
         if uu____429
         then g1
         else
           (let uu___87_431 = g1 in
            let uu____432 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___87_431.context);
              witness = (uu___87_431.witness);
              goal_ty = uu____432
            }))
let with_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with | [] -> fail "No more goals" | hd1::tl1 -> f hd1)
let cur_goal: goal tac =
  mk_tac
    (fun ps  ->
       match ps.goals with
       | hd1::uu____462 -> Success (hd1, ps)
       | uu____464 -> Failed ("No goals left", ps))
let set_cur_goal: goal -> Prims.unit tac =
  fun g  ->
    mk_tac
      (fun ps  ->
         match ps.goals with
         | hd1::tl1 ->
             Success
               ((),
                 (let uu___88_476 = ps in
                  {
                    main_context = (uu___88_476.main_context);
                    main_goal = (uu___88_476.main_goal);
                    all_implicits = (uu___88_476.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___88_476.smt_goals);
                    transaction = (uu___88_476.transaction)
                  }))
         | uu____477 -> Failed ("No goals left", ps))
let replace_point:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun e1  ->
    fun e2  ->
      fun t  ->
        let uu____488 = FStar_Syntax_Util.term_eq e1 t in
        if uu____488 then e2 else t
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
                 let uu____529 = FStar_TypeChecker_Rel.try_teq true env t1 t2 in
                 match uu____529 with
                 | None  -> false
                 | Some g1 -> FStar_TypeChecker_Rel.is_trivial g1 in
               if ok
               then
                 let goal_ty' = treplace env e1 e2 g.goal_ty in
                 let uu____534 =
                   set_cur_goal
                     (let uu___89_536 = g in
                      {
                        context = (uu___89_536.context);
                        witness = (uu___89_536.witness);
                        goal_ty = goal_ty'
                      }) in
                 bind uu____534
                   (fun uu____537  ->
                      let uu____538 =
                        let uu____540 =
                          let uu____541 =
                            FStar_Syntax_Util.mk_eq2
                              FStar_Syntax_Syntax.U_zero t1 e1 e2 in
                          {
                            context = (g.context);
                            witness = None;
                            goal_ty = uu____541
                          } in
                        [uu____540] in
                      add_goals uu____538)
               else
                 (FStar_TypeChecker_Err.add_errors env
                    [("Ill-type rewriting requested",
                       (e1.FStar_Syntax_Syntax.pos))];
                  fail "grewrite: Ill-typed rewriting requested"))
let smt: Prims.unit tac =
  with_cur_goal "smt"
    (fun g  ->
       bind dismiss
         (fun uu____550  ->
            let uu____551 =
              add_goals
                [(let uu___90_553 = g in
                  {
                    context = (uu___90_553.context);
                    witness = (uu___90_553.witness);
                    goal_ty = FStar_Syntax_Util.t_true
                  })] in
            bind uu____551 (fun uu____554  -> add_smt_goals [g])))
let focus_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___91_576 = p in
             {
               main_context = (uu___91_576.main_context);
               main_goal = (uu___91_576.main_goal);
               all_implicits = (uu___91_576.all_implicits);
               goals = [hd1];
               smt_goals = (uu___91_576.smt_goals);
               transaction = (uu___91_576.transaction)
             } in
           let uu____577 = set q in
           bind uu____577
             (fun uu____579  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___92_583 = q' in
                            {
                              main_context = (uu___92_583.main_context);
                              main_goal = (uu___92_583.main_goal);
                              all_implicits = (uu___92_583.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___92_583.smt_goals);
                              transaction = (uu___92_583.transaction)
                            } in
                          let uu____584 = set q2 in
                          bind uu____584 (fun uu____586  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | uu____620::[] -> bind f (fun a  -> ret (a, None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____635  ->
                let uu____636 = add_goals [hd1] in
                bind uu____636
                  (fun uu____641  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____649  ->
                               match uu____649 with
                               | { main_context = uu____654;
                                   main_goal = uu____655;
                                   all_implicits = uu____656;
                                   goals = sub_goals_f;
                                   smt_goals = uu____658;
                                   transaction = uu____659;_} ->
                                   bind dismiss_all
                                     (fun uu____665  ->
                                        let uu____666 = add_goals tl1 in
                                        bind uu____666
                                          (fun uu____671  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____676 =
                                                    add_goals sub_goals_f in
                                                  bind uu____676
                                                    (fun uu____681  ->
                                                       ret (a, (Some b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____704 = t1.tac_f p in
       match uu____704 with | Failed uu____707 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____725 =
         let uu____728 =
           let uu____734 = map t in cur_goal_and_rest t uu____734 in
         bind uu____728
           (fun uu___81_743  ->
              match uu___81_743 with
              | (hd1,None ) -> ret [hd1]
              | (hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____725 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal "map_goal"
        (fun g  ->
           let uu____776 =
             let uu___93_777 = g in
             let uu____778 = f g.goal_ty in
             {
               context = (uu___93_777.context);
               witness = (uu___93_777.witness);
               goal_ty = uu____778
             } in
           replace_cur uu____776) in
    let uu____779 = map aux in bind uu____779 (fun uu____783  -> ret ())
let map_meta t =
  with_cur_goal "map_meta"
    (fun g  ->
       let uu____796 =
         let uu____797 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____797.FStar_Syntax_Syntax.n in
       match uu____796 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____807 =
             replace_cur
               (let uu___94_809 = g in
                {
                  context = (uu___94_809.context);
                  witness = (uu___94_809.witness);
                  goal_ty = f
                }) in
           bind uu____807
             (fun uu____810  ->
                bind t
                  (fun a  ->
                     let uu____812 =
                       map_goal_term
                         (fun tm  ->
                            let uu____815 = is_true tm in
                            if uu____815
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____812 (fun uu____821  -> ret a)))
       | uu____822 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____835 =
        bind t1
          (fun uu____837  ->
             let uu____838 = map t2 in
             bind uu____838 (fun uu____842  -> ret ())) in
      focus_cur_goal "seq" uu____835
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal "intros"
    (fun goal  ->
       let uu____846 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____846 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____854  ->
                let uu____855 = add_goals [new_goal] in
                bind uu____855
                  (fun uu____857  ->
                     (let uu____859 =
                        FStar_Syntax_Print.binders_to_string ", " bs in
                      FStar_Util.print1 "intros: %s\n" uu____859);
                     ret bs))
       | uu____860 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____863  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____874 = let uu____880 = FStar_Syntax_Syntax.as_arg p in [uu____880] in
  FStar_Syntax_Util.mk_app sq uu____874
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____887 = FStar_Syntax_Util.head_and_args t in
    match uu____887 with
    | (head1,args) ->
        let uu____916 =
          let uu____924 =
            let uu____925 = FStar_Syntax_Util.un_uinst head1 in
            uu____925.FStar_Syntax_Syntax.n in
          (uu____924, args) in
        (match uu____916 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____938)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____958;
               FStar_Syntax_Syntax.index = uu____959;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____961;
                   FStar_Syntax_Syntax.pos = uu____962;
                   FStar_Syntax_Syntax.vars = uu____963;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____982 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal "imp_intro"
    (fun goal  ->
       let uu____994 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____994 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____999)::(rhs,uu____1001)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1029 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1029; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1030  ->
                let uu____1031 = add_goals [new_goal] in
                bind uu____1031
                  (fun uu____1033  ->
                     (let uu____1035 = FStar_Syntax_Print.bv_to_string name in
                      FStar_Util.print1 "imp_intro: %s\n" uu____1035);
                     (let uu____1036 = FStar_Syntax_Syntax.mk_binder name in
                      ret uu____1036)))
       | uu____1037 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal "split"
    (fun goal  ->
       let uu____1041 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1041 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1051  ->
                     match uu____1051 with
                     | (a,uu____1055) ->
                         let uu___95_1056 = goal in
                         {
                           context = (uu___95_1056.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1057  -> add_goals new_goals)
       | uu____1058 -> fail "Cannot split this goal; expected a conjunction")
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
       let uu____1065 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1065 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid ->
           bind dismiss
             (fun uu____1078  ->
                add_goals
                  [(let uu___96_1079 = goal in
                    {
                      context = (uu___96_1079.context);
                      witness = (uu___96_1079.witness);
                      goal_ty = t
                    })])
       | uu____1080 -> fail "Not a trivial goal")
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "apply_lemma"
      (fun goal  ->
         try
           let uu____1091 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1091 with
           | (tm1,t,guard) ->
               let uu____1099 =
                 let uu____1100 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1100 in
               if uu____1099
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1103 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1103 with
                  | (bs,comp) ->
                      let uu____1118 =
                        FStar_List.fold_left
                          (fun uu____1135  ->
                             fun uu____1136  ->
                               match (uu____1135, uu____1136) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1185 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1185 with
                                    | (u,uu____1200,g_u) ->
                                        let uu____1208 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1208,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1118 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1240 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1256 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1286 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1240 with
                            | (pre,post) ->
                                let uu____1309 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1309 with
                                 | None  ->
                                     fail
                                       "apply_lemma: does not unify with goal"
                                 | Some g ->
                                     let g1 =
                                       let uu____1314 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1314
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1350  ->
                                               match uu____1350 with
                                               | (uu____1357,uu____1358,uu____1359,tm2,uu____1361,uu____1362)
                                                   ->
                                                   let uu____1363 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1363 with
                                                    | (hd1,uu____1374) ->
                                                        let uu____1389 =
                                                          let uu____1390 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1390.FStar_Syntax_Syntax.n in
                                                        (match uu____1389
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1393 ->
                                                             true
                                                         | uu____1402 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____1406 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____1422  ->
                                                   match uu____1422 with
                                                   | (_msg,_env,_uvar,term,typ,uu____1434)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (Some term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___99_1435 = goal in
                                          {
                                            context = (uu___99_1435.context);
                                            witness = None;
                                            goal_ty = pre
                                          }) :: uu____1406 in
                                       let uu____1436 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1436
                                         (fun uu____1438  ->
                                            bind dismiss
                                              (fun uu____1439  ->
                                                 add_goals sub_goals))))))))
         with | uu____1442 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "exact"
      (fun goal  ->
         try
           let uu____1452 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1452 with
           | (uu____1457,t,guard) ->
               let uu____1460 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1460
               then
                 (solve goal tm;
                  replace_cur
                    (let uu___102_1463 = goal in
                     {
                       context = (uu___102_1463.context);
                       witness = None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____1466 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1467 = FStar_Syntax_Print.term_to_string t in
                    let uu____1468 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1466
                      uu____1467 uu____1468 in
                  fail msg)
         with
         | e ->
             let uu____1472 =
               let uu____1473 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1473 in
             fail uu____1472)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal "rewrite"
      (fun goal  ->
         (let uu____1481 = FStar_Syntax_Print.bv_to_string (Prims.fst h) in
          let uu____1482 =
            FStar_Syntax_Print.term_to_string
              (Prims.fst h).FStar_Syntax_Syntax.sort in
          FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1481 uu____1482);
         (let uu____1483 =
            let uu____1485 =
              let uu____1486 =
                FStar_TypeChecker_Env.lookup_bv goal.context (Prims.fst h) in
              FStar_All.pipe_left Prims.fst uu____1486 in
            FStar_Syntax_Util.destruct_typ_as_formula uu____1485 in
          match uu____1483 with
          | Some (FStar_Syntax_Util.BaseConn
              (l,uu____1493::(x,uu____1495)::(e,uu____1497)::[])) when
              FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
              let uu____1531 =
                let uu____1532 = FStar_Syntax_Subst.compress x in
                uu____1532.FStar_Syntax_Syntax.n in
              (match uu____1531 with
               | FStar_Syntax_Syntax.Tm_name x1 ->
                   let goal1 =
                     let uu___103_1538 = goal in
                     let uu____1539 =
                       FStar_Syntax_Subst.subst
                         [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                     {
                       context = (uu___103_1538.context);
                       witness = (uu___103_1538.witness);
                       goal_ty = uu____1539
                     } in
                   replace_cur goal1
               | uu____1542 ->
                   fail
                     "Not an equality hypothesis with a variable on the LHS")
          | uu____1543 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal "clear"
    (fun goal  ->
       let uu____1547 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1547 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1560 = FStar_Util.set_mem x fns in
           if uu____1560
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___104_1564 = goal in
                {
                  context = env';
                  witness = (uu___104_1564.witness);
                  goal_ty = (uu___104_1564.goal_ty)
                } in
              bind dismiss (fun uu____1565  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "clear_hd"
      (fun goal  ->
         let uu____1572 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1572 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal "revert"
    (fun goal  ->
       let uu____1587 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1587 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1601 = FStar_Util.set_mem x fvs in
             if uu____1601
             then
               let uu___105_1602 = goal in
               let uu____1603 =
                 let uu____1604 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1604 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___105_1602.witness);
                 goal_ty = uu____1603
               }
             else
               (let uu___106_1606 = goal in
                let uu____1607 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___106_1606.witness);
                  goal_ty = uu____1607
                }) in
           bind dismiss (fun uu____1608  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "revert_hd"
      (fun goal  ->
         let uu____1615 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1615 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1627 =
                 let uu____1628 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1629 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1628 uu____1629 in
               fail uu____1627
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1642 = revert_all_hd xs1 in
        bind uu____1642 (fun uu____1644  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1648 =
      let uu____1649 = FStar_Syntax_Subst.compress x in
      uu____1649.FStar_Syntax_Syntax.n in
    match uu____1648 with
    | FStar_Syntax_Syntax.Tm_name uu____1652 -> true
    | uu____1653 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1657 =
      let uu____1658 = FStar_Syntax_Subst.compress x in
      uu____1658.FStar_Syntax_Syntax.n in
    match uu____1657 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1662 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun t  ->
    let uu____1674 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1674 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____1686)::(rhs,uu____1688)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____1714 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____1714 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____1786 =
               let uu____1794 = as_name x in (uu____1794, e, rhs) in
             Some uu____1786
         | uu____1806 -> None)
    | uu____1815 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____1838 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____1847 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____1847
           then
             let uu____1849 =
               let uu___107_1850 = p in
               let uu____1851 =
                 let uu____1853 = conj_goals g1 g2 in uu____1853 :: rest in
               {
                 main_context = (uu___107_1850.main_context);
                 main_goal = (uu___107_1850.main_goal);
                 all_implicits = (uu___107_1850.all_implicits);
                 goals = uu____1851;
                 smt_goals = (uu___107_1850.smt_goals);
                 transaction = (uu___107_1850.transaction)
               } in
             set uu____1849
           else
             (let g1_binders =
                let uu____1856 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____1856
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____1858 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____1858
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____1859 =
                let uu____1860 = goal_to_string g1 in
                let uu____1861 = goal_to_string g2 in
                let uu____1862 =
                  let uu____1863 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____1863 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____1860 uu____1861 uu____1862 in
              fail uu____1859)
       | uu____1864 ->
           let goals =
             let uu____1867 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____1867 (FStar_String.concat "\n\t") in
           let uu____1873 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____1873)
let rec visit: Prims.unit tac -> Prims.unit tac =
  fun callback  ->
    let uu____1881 =
      let uu____1883 =
        with_cur_goal "visit_strengthen_else"
          (fun goal  ->
             let uu____1886 =
               FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
             match uu____1886 with
             | None  ->
                 let uu____1889 =
                   let uu____1890 = FStar_Syntax_Subst.compress goal.goal_ty in
                   uu____1890.FStar_Syntax_Syntax.n in
                 (match uu____1889 with
                  | FStar_Syntax_Syntax.Tm_meta uu____1894 ->
                      let uu____1899 = visit callback in map_meta uu____1899
                  | uu____1901 ->
                      ((let uu____1903 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        FStar_Util.print1 "Not a formula, split to smt %s\n"
                          uu____1903);
                       smt))
             | Some (FStar_Syntax_Util.QEx uu____1904) ->
                 ((let uu____1909 =
                     FStar_Syntax_Print.term_to_string goal.goal_ty in
                   FStar_Util.print1
                     "Not yet handled: exists\n\tGoal is %s\n" uu____1909);
                  ret ())
             | Some (FStar_Syntax_Util.QAll (xs,uu____1911,uu____1912)) ->
                 bind intros
                   (fun binders  ->
                      let uu____1914 = visit callback in
                      let uu____1916 =
                        let uu____1918 =
                          let uu____1920 = FStar_List.map Prims.fst binders in
                          revert_all_hd uu____1920 in
                        bind uu____1918
                          (fun uu____1924  ->
                             with_cur_goal "inner"
                               (fun goal1  ->
                                  (let uu____1927 = goal_to_string goal1 in
                                   FStar_Util.print1
                                     "After reverting intros, goal is %s\n"
                                     uu____1927);
                                  ret ())) in
                      seq uu____1914 uu____1916)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____1929)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
                 let uu____1930 =
                   let uu____1932 = visit callback in seq split uu____1932 in
                 bind uu____1930 (fun uu____1934  -> merge_sub_goals)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____1936)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
                 bind imp_intro
                   (fun h  ->
                      let uu____1938 = visit callback in
                      seq uu____1938 revert)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____1941)) ->
                 or_else trivial smt) in
      or_else callback uu____1883 in
    focus_cur_goal "visit_strengthen" uu____1881
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> proofstate =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____1949 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____1949 } in
      let uu____1950 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____1950
      }