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
let dump_goal ps goal =
  let uu____287 = goal_to_string goal in
  FStar_Util.print1 "TAC>> %s\n" uu____287
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Util.print1 "TAC>> State dump (%s):\n" msg;
      (let uu____296 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       FStar_Util.print1 "TAC>> ACTIVE goals (%s):\n" uu____296);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____302 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       FStar_Util.print1 "TAC>> SMT goals (%s):\n" uu____302);
      FStar_List.iter (dump_goal ps) ps.smt_goals
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let log ps f =
  let uu____333 = FStar_ST.read tacdbg in if uu____333 then f () else ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg = mk_tac (fun p  -> Failed (msg, p))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____363  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      match goal.witness with
      | None  -> ()
      | Some w ->
          let uu____371 =
            FStar_TypeChecker_Rel.teq_nosmt goal.context w solution in
          if uu____371
          then ()
          else
            (let uu____373 =
               let uu____374 =
                 let uu____375 = FStar_Syntax_Print.term_to_string solution in
                 let uu____376 = FStar_Syntax_Print.term_to_string w in
                 let uu____377 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 FStar_Util.format3 "%s does not solve %s : %s" uu____375
                   uu____376 uu____377 in
               Failure uu____374 in
             Prims.raise uu____373)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____380 =
         let uu___82_381 = p in
         let uu____382 = FStar_List.tl p.goals in
         {
           main_context = (uu___82_381.main_context);
           main_goal = (uu___82_381.main_goal);
           all_implicits = (uu___82_381.all_implicits);
           goals = uu____382;
           smt_goals = (uu___82_381.smt_goals);
           transaction = (uu___82_381.transaction)
         } in
       set uu____380)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___83_386 = p in
          {
            main_context = (uu___83_386.main_context);
            main_goal = (uu___83_386.main_goal);
            all_implicits = (uu___83_386.all_implicits);
            goals = [];
            smt_goals = (uu___83_386.smt_goals);
            transaction = (uu___83_386.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_395 = p in
            {
              main_context = (uu___84_395.main_context);
              main_goal = (uu___84_395.main_goal);
              all_implicits = (uu___84_395.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___84_395.smt_goals);
              transaction = (uu___84_395.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___85_404 = p in
            {
              main_context = (uu___85_404.main_context);
              main_goal = (uu___85_404.main_goal);
              all_implicits = (uu___85_404.all_implicits);
              goals = (uu___85_404.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___85_404.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____410  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___86_417 = p in
            {
              main_context = (uu___86_417.main_context);
              main_goal = (uu___86_417.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___86_417.goals);
              smt_goals = (uu___86_417.smt_goals);
              transaction = (uu___86_417.transaction)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____427 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____427 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid
    | uu____439 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____444 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____444 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid
    | uu____456 -> false
let conj_goals: goal -> goal -> goal =
  fun g1  ->
    fun g2  ->
      let t1 = g1.goal_ty in
      let t2 = g2.goal_ty in
      let uu____466 = (is_true t1) || (is_false t2) in
      if uu____466
      then g2
      else
        (let uu____468 = (is_true t2) || (is_false t1) in
         if uu____468
         then g1
         else
           (let uu___87_470 = g1 in
            let uu____471 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___87_470.context);
              witness = (uu___87_470.witness);
              goal_ty = uu____471
            }))
let with_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with | [] -> fail "No more goals" | hd1::tl1 -> f hd1)
let cur_goal: goal tac =
  mk_tac
    (fun ps  ->
       match ps.goals with
       | hd1::uu____501 -> Success (hd1, ps)
       | uu____503 -> Failed ("No goals left", ps))
let set_cur_goal: goal -> Prims.unit tac =
  fun g  ->
    mk_tac
      (fun ps  ->
         match ps.goals with
         | hd1::tl1 ->
             Success
               ((),
                 (let uu___88_515 = ps in
                  {
                    main_context = (uu___88_515.main_context);
                    main_goal = (uu___88_515.main_goal);
                    all_implicits = (uu___88_515.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___88_515.smt_goals);
                    transaction = (uu___88_515.transaction)
                  }))
         | uu____516 -> Failed ("No goals left", ps))
let replace_point:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun e1  ->
    fun e2  ->
      fun t  ->
        let uu____527 = FStar_Syntax_Util.term_eq e1 t in
        if uu____527 then e2 else t
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
                 let uu____568 = FStar_TypeChecker_Rel.try_teq true env t1 t2 in
                 match uu____568 with
                 | None  -> false
                 | Some g1 -> FStar_TypeChecker_Rel.is_trivial g1 in
               if ok
               then
                 let goal_ty' = treplace env e1 e2 g.goal_ty in
                 let uu____573 =
                   set_cur_goal
                     (let uu___89_575 = g in
                      {
                        context = (uu___89_575.context);
                        witness = (uu___89_575.witness);
                        goal_ty = goal_ty'
                      }) in
                 bind uu____573
                   (fun uu____576  ->
                      let uu____577 =
                        let uu____579 =
                          let uu____580 =
                            FStar_Syntax_Util.mk_eq2
                              FStar_Syntax_Syntax.U_zero t1 e1 e2 in
                          {
                            context = (g.context);
                            witness = None;
                            goal_ty = uu____580
                          } in
                        [uu____579] in
                      add_goals uu____577)
               else
                 (FStar_TypeChecker_Err.add_errors env
                    [("Ill-type rewriting requested",
                       (e1.FStar_Syntax_Syntax.pos))];
                  fail "grewrite: Ill-typed rewriting requested"))
let smt: Prims.unit tac =
  with_cur_goal "smt"
    (fun g  ->
       bind dismiss
         (fun uu____589  ->
            let uu____590 =
              add_goals
                [(let uu___90_592 = g in
                  {
                    context = (uu___90_592.context);
                    witness = (uu___90_592.witness);
                    goal_ty = FStar_Syntax_Util.t_true
                  })] in
            bind uu____590 (fun uu____593  -> add_smt_goals [g])))
let focus_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___91_615 = p in
             {
               main_context = (uu___91_615.main_context);
               main_goal = (uu___91_615.main_goal);
               all_implicits = (uu___91_615.all_implicits);
               goals = [hd1];
               smt_goals = (uu___91_615.smt_goals);
               transaction = (uu___91_615.transaction)
             } in
           let uu____616 = set q in
           bind uu____616
             (fun uu____618  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___92_622 = q' in
                            {
                              main_context = (uu___92_622.main_context);
                              main_goal = (uu___92_622.main_goal);
                              all_implicits = (uu___92_622.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___92_622.smt_goals);
                              transaction = (uu___92_622.transaction)
                            } in
                          let uu____623 = set q2 in
                          bind uu____623 (fun uu____625  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | uu____659::[] -> bind f (fun a  -> ret (a, None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____674  ->
                let uu____675 = add_goals [hd1] in
                bind uu____675
                  (fun uu____680  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____688  ->
                               match uu____688 with
                               | { main_context = uu____693;
                                   main_goal = uu____694;
                                   all_implicits = uu____695;
                                   goals = sub_goals_f;
                                   smt_goals = uu____697;
                                   transaction = uu____698;_} ->
                                   bind dismiss_all
                                     (fun uu____704  ->
                                        let uu____705 = add_goals tl1 in
                                        bind uu____705
                                          (fun uu____710  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____715 =
                                                    add_goals sub_goals_f in
                                                  bind uu____715
                                                    (fun uu____720  ->
                                                       ret (a, (Some b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____743 = t1.tac_f p in
       match uu____743 with | Failed uu____746 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____764 =
         let uu____767 =
           let uu____773 = map t in cur_goal_and_rest t uu____773 in
         bind uu____767
           (fun uu___81_782  ->
              match uu___81_782 with
              | (hd1,None ) -> ret [hd1]
              | (hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____764 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal "map_goal"
        (fun g  ->
           let uu____815 =
             let uu___93_816 = g in
             let uu____817 = f g.goal_ty in
             {
               context = (uu___93_816.context);
               witness = (uu___93_816.witness);
               goal_ty = uu____817
             } in
           replace_cur uu____815) in
    let uu____818 = map aux in bind uu____818 (fun uu____822  -> ret ())
let map_meta t =
  with_cur_goal "map_meta"
    (fun g  ->
       let uu____835 =
         let uu____836 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____836.FStar_Syntax_Syntax.n in
       match uu____835 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____846 =
             replace_cur
               (let uu___94_848 = g in
                {
                  context = (uu___94_848.context);
                  witness = (uu___94_848.witness);
                  goal_ty = f
                }) in
           bind uu____846
             (fun uu____849  ->
                bind t
                  (fun a  ->
                     let uu____851 =
                       map_goal_term
                         (fun tm  ->
                            let uu____854 = is_true tm in
                            if uu____854
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____851 (fun uu____860  -> ret a)))
       | uu____861 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____874 =
        bind t1
          (fun uu____876  ->
             let uu____877 = map t2 in
             bind uu____877 (fun uu____881  -> ret ())) in
      focus_cur_goal "seq" uu____874
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal "intros"
    (fun goal  ->
       let uu____885 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____885 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____893  ->
                let uu____894 = add_goals [new_goal] in
                bind uu____894
                  (fun uu____896  ->
                     let uu____897 =
                       FStar_All.pipe_left mlog
                         (fun uu____902  ->
                            let uu____903 =
                              FStar_Syntax_Print.binders_to_string ", " bs in
                            FStar_Util.print1 "intros: %s\n" uu____903) in
                     bind uu____897 (fun uu____904  -> ret bs)))
       | uu____905 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____908  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____919 = let uu____925 = FStar_Syntax_Syntax.as_arg p in [uu____925] in
  FStar_Syntax_Util.mk_app sq uu____919
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____932 = FStar_Syntax_Util.head_and_args t in
    match uu____932 with
    | (head1,args) ->
        let uu____961 =
          let uu____969 =
            let uu____970 = FStar_Syntax_Util.un_uinst head1 in
            uu____970.FStar_Syntax_Syntax.n in
          (uu____969, args) in
        (match uu____961 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____983)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1003;
               FStar_Syntax_Syntax.index = uu____1004;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1006;
                   FStar_Syntax_Syntax.pos = uu____1007;
                   FStar_Syntax_Syntax.vars = uu____1008;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____1027 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal "imp_intro"
    (fun goal  ->
       let uu____1039 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1039 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1044)::(rhs,uu____1046)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1074 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1074; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1075  ->
                let uu____1076 = add_goals [new_goal] in
                bind uu____1076
                  (fun uu____1078  ->
                     let uu____1079 =
                       FStar_All.pipe_left mlog
                         (fun uu____1084  ->
                            let uu____1085 =
                              FStar_Syntax_Print.bv_to_string name in
                            FStar_Util.print1 "imp_intro: %s\n" uu____1085) in
                     bind uu____1079
                       (fun uu____1086  ->
                          let uu____1087 = FStar_Syntax_Syntax.mk_binder name in
                          ret uu____1087)))
       | uu____1088 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal "split"
    (fun goal  ->
       let uu____1092 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1092 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1102  ->
                     match uu____1102 with
                     | (a,uu____1106) ->
                         let uu___95_1107 = goal in
                         {
                           context = (uu___95_1107.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1108  -> add_goals new_goals)
       | uu____1109 -> fail "Cannot split this goal; expected a conjunction")
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
       let uu____1116 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1116 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid ->
           bind dismiss
             (fun uu____1129  ->
                add_goals
                  [(let uu___96_1130 = goal in
                    {
                      context = (uu___96_1130.context);
                      witness = (uu___96_1130.witness);
                      goal_ty = t
                    })])
       | uu____1131 -> fail "Not a trivial goal")
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "apply_lemma"
      (fun goal  ->
         try
           let uu____1142 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1142 with
           | (tm1,t,guard) ->
               let uu____1150 =
                 let uu____1151 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1151 in
               if uu____1150
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1154 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1154 with
                  | (bs,comp) ->
                      let uu____1169 =
                        FStar_List.fold_left
                          (fun uu____1186  ->
                             fun uu____1187  ->
                               match (uu____1186, uu____1187) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1236 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1236 with
                                    | (u,uu____1251,g_u) ->
                                        let uu____1259 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1259,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1169 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1291 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1307 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1337 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1291 with
                            | (pre,post) ->
                                let uu____1360 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1360 with
                                 | None  ->
                                     fail
                                       "apply_lemma: does not unify with goal"
                                 | Some g ->
                                     let g1 =
                                       let uu____1365 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1365
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1401  ->
                                               match uu____1401 with
                                               | (uu____1408,uu____1409,uu____1410,tm2,uu____1412,uu____1413)
                                                   ->
                                                   let uu____1414 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1414 with
                                                    | (hd1,uu____1425) ->
                                                        let uu____1440 =
                                                          let uu____1441 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1441.FStar_Syntax_Syntax.n in
                                                        (match uu____1440
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1444 ->
                                                             true
                                                         | uu____1453 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____1457 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____1473  ->
                                                   match uu____1473 with
                                                   | (_msg,_env,_uvar,term,typ,uu____1485)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (Some term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___99_1486 = goal in
                                          {
                                            context = (uu___99_1486.context);
                                            witness = None;
                                            goal_ty = pre
                                          }) :: uu____1457 in
                                       let uu____1487 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1487
                                         (fun uu____1489  ->
                                            bind dismiss
                                              (fun uu____1490  ->
                                                 add_goals sub_goals))))))))
         with | uu____1493 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "exact"
      (fun goal  ->
         try
           let uu____1503 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1503 with
           | (uu____1508,t,guard) ->
               let uu____1511 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1511
               then
                 (solve goal tm;
                  replace_cur
                    (let uu___102_1514 = goal in
                     {
                       context = (uu___102_1514.context);
                       witness = None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____1517 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1518 = FStar_Syntax_Print.term_to_string t in
                    let uu____1519 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1517
                      uu____1518 uu____1519 in
                  fail msg)
         with
         | e ->
             let uu____1523 =
               let uu____1524 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1524 in
             fail uu____1523)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal "rewrite"
      (fun goal  ->
         let uu____1531 =
           FStar_All.pipe_left mlog
             (fun uu____1536  ->
                let uu____1537 =
                  FStar_Syntax_Print.bv_to_string (Prims.fst h) in
                let uu____1538 =
                  FStar_Syntax_Print.term_to_string
                    (Prims.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1537
                  uu____1538) in
         bind uu____1531
           (fun uu____1539  ->
              let uu____1540 =
                let uu____1542 =
                  let uu____1543 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (Prims.fst h) in
                  FStar_All.pipe_left Prims.fst uu____1543 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1542 in
              match uu____1540 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1550::(x,uu____1552)::(e,uu____1554)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____1588 =
                    let uu____1589 = FStar_Syntax_Subst.compress x in
                    uu____1589.FStar_Syntax_Syntax.n in
                  (match uu____1588 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___103_1595 = goal in
                         let uu____1596 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___103_1595.context);
                           witness = (uu___103_1595.witness);
                           goal_ty = uu____1596
                         } in
                       replace_cur goal1
                   | uu____1599 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____1600 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal "clear"
    (fun goal  ->
       let uu____1604 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1604 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1617 = FStar_Util.set_mem x fns in
           if uu____1617
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___104_1621 = goal in
                {
                  context = env';
                  witness = (uu___104_1621.witness);
                  goal_ty = (uu___104_1621.goal_ty)
                } in
              bind dismiss (fun uu____1622  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "clear_hd"
      (fun goal  ->
         let uu____1629 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1629 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal "revert"
    (fun goal  ->
       let uu____1644 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1644 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1658 = FStar_Util.set_mem x fvs in
             if uu____1658
             then
               let uu___105_1659 = goal in
               let uu____1660 =
                 let uu____1661 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1661 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___105_1659.witness);
                 goal_ty = uu____1660
               }
             else
               (let uu___106_1663 = goal in
                let uu____1664 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___106_1663.witness);
                  goal_ty = uu____1664
                }) in
           bind dismiss (fun uu____1665  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "revert_hd"
      (fun goal  ->
         let uu____1672 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1672 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1684 =
                 let uu____1685 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1686 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1685 uu____1686 in
               fail uu____1684
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1699 = revert_all_hd xs1 in
        bind uu____1699 (fun uu____1701  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1705 =
      let uu____1706 = FStar_Syntax_Subst.compress x in
      uu____1706.FStar_Syntax_Syntax.n in
    match uu____1705 with
    | FStar_Syntax_Syntax.Tm_name uu____1709 -> true
    | uu____1710 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1714 =
      let uu____1715 = FStar_Syntax_Subst.compress x in
      uu____1715.FStar_Syntax_Syntax.n in
    match uu____1714 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1719 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun t  ->
    let uu____1731 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1731 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____1743)::(rhs,uu____1745)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____1771 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____1771 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____1843 =
               let uu____1851 = as_name x in (uu____1851, e, rhs) in
             Some uu____1843
         | uu____1863 -> None)
    | uu____1872 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____1895 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____1904 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____1904
           then
             let uu____1906 =
               let uu___107_1907 = p in
               let uu____1908 =
                 let uu____1910 = conj_goals g1 g2 in uu____1910 :: rest in
               {
                 main_context = (uu___107_1907.main_context);
                 main_goal = (uu___107_1907.main_goal);
                 all_implicits = (uu___107_1907.all_implicits);
                 goals = uu____1908;
                 smt_goals = (uu___107_1907.smt_goals);
                 transaction = (uu___107_1907.transaction)
               } in
             set uu____1906
           else
             (let g1_binders =
                let uu____1913 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____1913
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____1915 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____1915
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____1916 =
                let uu____1917 = goal_to_string g1 in
                let uu____1918 = goal_to_string g2 in
                let uu____1919 =
                  let uu____1920 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____1920 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____1917 uu____1918 uu____1919 in
              fail uu____1916)
       | uu____1921 ->
           let goals =
             let uu____1924 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____1924 (FStar_String.concat "\n\t") in
           let uu____1930 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____1930)
let rec visit: Prims.unit tac -> Prims.unit tac =
  fun callback  ->
    let uu____1938 =
      let uu____1940 =
        with_cur_goal "visit_strengthen_else"
          (fun goal  ->
             let uu____1943 =
               FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
             match uu____1943 with
             | None  ->
                 let uu____1946 =
                   let uu____1947 = FStar_Syntax_Subst.compress goal.goal_ty in
                   uu____1947.FStar_Syntax_Syntax.n in
                 (match uu____1946 with
                  | FStar_Syntax_Syntax.Tm_meta uu____1951 ->
                      let uu____1956 = visit callback in map_meta uu____1956
                  | uu____1958 ->
                      let uu____1959 =
                        FStar_All.pipe_left mlog
                          (fun uu____1964  ->
                             let uu____1965 =
                               FStar_Syntax_Print.term_to_string goal.goal_ty in
                             FStar_Util.print1
                               "Not a formula, split to smt %s\n" uu____1965) in
                      bind uu____1959 (fun uu____1966  -> smt))
             | Some (FStar_Syntax_Util.QEx uu____1967) ->
                 let uu____1971 =
                   FStar_All.pipe_left mlog
                     (fun uu____1976  ->
                        let uu____1977 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        FStar_Util.print1
                          "Not yet handled: exists\n\tGoal is %s\n"
                          uu____1977) in
                 bind uu____1971 (fun uu____1978  -> ret ())
             | Some (FStar_Syntax_Util.QAll (xs,uu____1980,uu____1981)) ->
                 bind intros
                   (fun binders  ->
                      let uu____1983 = visit callback in
                      let uu____1985 =
                        let uu____1987 =
                          let uu____1989 = FStar_List.map Prims.fst binders in
                          revert_all_hd uu____1989 in
                        bind uu____1987
                          (fun uu____1993  ->
                             with_cur_goal "inner"
                               (fun goal1  ->
                                  let uu____1995 =
                                    FStar_All.pipe_left mlog
                                      (fun uu____2000  ->
                                         let uu____2001 =
                                           goal_to_string goal1 in
                                         FStar_Util.print1
                                           "After reverting intros, goal is %s\n"
                                           uu____2001) in
                                  bind uu____1995 (fun uu____2002  -> ret ()))) in
                      seq uu____1983 uu____1985)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2004)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
                 let uu____2005 =
                   let uu____2007 = visit callback in seq split uu____2007 in
                 bind uu____2005 (fun uu____2009  -> merge_sub_goals)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2011)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
                 bind imp_intro
                   (fun h  ->
                      let uu____2013 = visit callback in
                      seq uu____2013 revert)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2016)) ->
                 or_else trivial smt) in
      or_else callback uu____1940 in
    focus_cur_goal "visit_strengthen" uu____1938
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2020 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2024 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2028 -> false
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
        let uu____2045 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2045 } in
      let uu____2046 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2046
      }