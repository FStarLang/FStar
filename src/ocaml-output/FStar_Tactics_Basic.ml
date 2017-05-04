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
    (fun g  ->
       bind dismiss
         (fun uu____620  ->
            let uu____621 =
              add_goals
                [(let uu___90_623 = g in
                  {
                    context = (uu___90_623.context);
                    witness = (uu___90_623.witness);
                    goal_ty = FStar_Syntax_Util.t_true
                  })] in
            bind uu____621 (fun uu____624  -> add_smt_goals [g])))
let focus_cur_goal f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___91_641 = p in
             {
               main_context = (uu___91_641.main_context);
               main_goal = (uu___91_641.main_goal);
               all_implicits = (uu___91_641.all_implicits);
               goals = [hd1];
               smt_goals = (uu___91_641.smt_goals);
               transaction = (uu___91_641.transaction)
             } in
           let uu____642 = set q in
           bind uu____642
             (fun uu____644  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___92_648 = q' in
                            {
                              main_context = (uu___92_648.main_context);
                              main_goal = (uu___92_648.main_goal);
                              all_implicits = (uu___92_648.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___92_648.smt_goals);
                              transaction = (uu___92_648.transaction)
                            } in
                          let uu____649 = set q2 in
                          bind uu____649 (fun uu____651  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | uu____685::[] -> bind f (fun a  -> ret (a, None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____700  ->
                let uu____701 = add_goals [hd1] in
                bind uu____701
                  (fun uu____706  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____714  ->
                               match uu____714 with
                               | { main_context = uu____719;
                                   main_goal = uu____720;
                                   all_implicits = uu____721;
                                   goals = sub_goals_f;
                                   smt_goals = uu____723;
                                   transaction = uu____724;_} ->
                                   bind dismiss_all
                                     (fun uu____730  ->
                                        let uu____731 = add_goals tl1 in
                                        bind uu____731
                                          (fun uu____736  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____741 =
                                                    add_goals sub_goals_f in
                                                  bind uu____741
                                                    (fun uu____746  ->
                                                       ret (a, (Some b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____769 = t1.tac_f p in
       match uu____769 with | Failed uu____772 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____790 =
         let uu____793 =
           let uu____799 = map t in cur_goal_and_rest t uu____799 in
         bind uu____793
           (fun uu___81_808  ->
              match uu___81_808 with
              | (hd1,None ) -> ret [hd1]
              | (hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____790 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal
        (fun g  ->
           let uu____841 =
             let uu___93_842 = g in
             let uu____843 = f g.goal_ty in
             {
               context = (uu___93_842.context);
               witness = (uu___93_842.witness);
               goal_ty = uu____843
             } in
           replace_cur uu____841) in
    let uu____844 = map aux in bind uu____844 (fun uu____848  -> ret ())
let map_meta t =
  with_cur_goal
    (fun g  ->
       let uu____861 =
         let uu____862 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____862.FStar_Syntax_Syntax.n in
       match uu____861 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____872 =
             replace_cur
               (let uu___94_874 = g in
                {
                  context = (uu___94_874.context);
                  witness = (uu___94_874.witness);
                  goal_ty = f
                }) in
           bind uu____872
             (fun uu____875  ->
                bind t
                  (fun a  ->
                     let uu____877 =
                       map_goal_term
                         (fun tm  ->
                            let uu____880 = is_true tm in
                            if uu____880
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____877 (fun uu____886  -> ret a)))
       | uu____887 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____900 =
        bind t1
          (fun uu____902  ->
             let uu____903 = map t2 in
             bind uu____903 (fun uu____907  -> ret ())) in
      focus_cur_goal uu____900
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal
    (fun goal  ->
       let uu____911 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____911 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____919  ->
                let uu____920 = add_goals [new_goal] in
                bind uu____920
                  (fun uu____922  ->
                     let uu____923 =
                       FStar_All.pipe_left mlog
                         (fun uu____928  ->
                            let uu____929 =
                              FStar_Syntax_Print.binders_to_string ", " bs in
                            FStar_Util.print1 "intros: %s\n" uu____929) in
                     bind uu____923 (fun uu____930  -> ret bs)))
       | uu____931 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____934  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____945 = let uu____951 = FStar_Syntax_Syntax.as_arg p in [uu____951] in
  FStar_Syntax_Util.mk_app sq uu____945
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____958 = FStar_Syntax_Util.head_and_args t in
    match uu____958 with
    | (head1,args) ->
        let uu____987 =
          let uu____995 =
            let uu____996 = FStar_Syntax_Util.un_uinst head1 in
            uu____996.FStar_Syntax_Syntax.n in
          (uu____995, args) in
        (match uu____987 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____1009)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1029;
               FStar_Syntax_Syntax.index = uu____1030;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1032;
                   FStar_Syntax_Syntax.pos = uu____1033;
                   FStar_Syntax_Syntax.vars = uu____1034;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____1053 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal
    (fun goal  ->
       let uu____1065 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1065 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1070)::(rhs,uu____1072)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1100 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1100; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1101  ->
                let uu____1102 = add_goals [new_goal] in
                bind uu____1102
                  (fun uu____1104  ->
                     let uu____1105 =
                       FStar_All.pipe_left mlog
                         (fun uu____1110  ->
                            let uu____1111 =
                              FStar_Syntax_Print.bv_to_string name in
                            FStar_Util.print1 "imp_intro: %s\n" uu____1111) in
                     bind uu____1105
                       (fun uu____1112  ->
                          let uu____1113 = FStar_Syntax_Syntax.mk_binder name in
                          ret uu____1113)))
       | uu____1114 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1118 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1118 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1128  ->
                     match uu____1128 with
                     | (a,uu____1132) ->
                         let uu___95_1133 = goal in
                         {
                           context = (uu___95_1133.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1134  -> add_goals new_goals)
       | uu____1135 -> fail "Cannot split this goal; expected a conjunction")
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
       let uu____1142 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1142 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid ->
           bind dismiss
             (fun uu____1155  ->
                add_goals
                  [(let uu___96_1156 = goal in
                    {
                      context = (uu___96_1156.context);
                      witness = (uu___96_1156.witness);
                      goal_ty = t
                    })])
       | uu____1157 -> fail "Not a trivial goal")
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1168 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1168 with
           | (tm1,t,guard) ->
               let uu____1176 =
                 let uu____1177 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1177 in
               if uu____1176
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1180 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1180 with
                  | (bs,comp) ->
                      let uu____1195 =
                        FStar_List.fold_left
                          (fun uu____1212  ->
                             fun uu____1213  ->
                               match (uu____1212, uu____1213) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1262 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1262 with
                                    | (u,uu____1277,g_u) ->
                                        let uu____1285 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1285,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1195 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1317 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1333 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1363 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1317 with
                            | (pre,post) ->
                                let uu____1386 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1386 with
                                 | None  ->
                                     fail
                                       "apply_lemma: does not unify with goal"
                                 | Some g ->
                                     let g1 =
                                       let uu____1391 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1391
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1427  ->
                                               match uu____1427 with
                                               | (uu____1434,uu____1435,uu____1436,tm2,uu____1438,uu____1439)
                                                   ->
                                                   let uu____1440 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1440 with
                                                    | (hd1,uu____1451) ->
                                                        let uu____1466 =
                                                          let uu____1467 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1467.FStar_Syntax_Syntax.n in
                                                        (match uu____1466
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1470 ->
                                                             true
                                                         | uu____1479 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____1483 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____1499  ->
                                                   match uu____1499 with
                                                   | (_msg,_env,_uvar,term,typ,uu____1511)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (Some term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___99_1512 = goal in
                                          {
                                            context = (uu___99_1512.context);
                                            witness = None;
                                            goal_ty = pre
                                          }) :: uu____1483 in
                                       let uu____1513 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1513
                                         (fun uu____1515  ->
                                            bind dismiss
                                              (fun uu____1516  ->
                                                 add_goals sub_goals))))))))
         with | uu____1519 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1529 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1529 with
           | (uu____1534,t,guard) ->
               let uu____1537 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1537
               then
                 (solve goal tm;
                  replace_cur
                    (let uu___102_1540 = goal in
                     {
                       context = (uu___102_1540.context);
                       witness = None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____1543 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1544 = FStar_Syntax_Print.term_to_string t in
                    let uu____1545 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1543
                      uu____1544 uu____1545 in
                  fail msg)
         with
         | e ->
             let uu____1549 =
               let uu____1550 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1550 in
             fail uu____1549)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal
      (fun goal  ->
         let uu____1557 =
           FStar_All.pipe_left mlog
             (fun uu____1562  ->
                let uu____1563 =
                  FStar_Syntax_Print.bv_to_string (Prims.fst h) in
                let uu____1564 =
                  FStar_Syntax_Print.term_to_string
                    (Prims.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1563
                  uu____1564) in
         bind uu____1557
           (fun uu____1565  ->
              let uu____1566 =
                let uu____1568 =
                  let uu____1569 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (Prims.fst h) in
                  FStar_All.pipe_left Prims.fst uu____1569 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1568 in
              match uu____1566 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1576::(x,uu____1578)::(e,uu____1580)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____1614 =
                    let uu____1615 = FStar_Syntax_Subst.compress x in
                    uu____1615.FStar_Syntax_Syntax.n in
                  (match uu____1614 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___103_1621 = goal in
                         let uu____1622 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___103_1621.context);
                           witness = (uu___103_1621.witness);
                           goal_ty = uu____1622
                         } in
                       replace_cur goal1
                   | uu____1625 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____1626 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1630 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1630 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1643 = FStar_Util.set_mem x fns in
           if uu____1643
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___104_1647 = goal in
                {
                  context = env';
                  witness = (uu___104_1647.witness);
                  goal_ty = (uu___104_1647.goal_ty)
                } in
              bind dismiss (fun uu____1648  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1655 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1655 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1670 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1670 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1684 = FStar_Util.set_mem x fvs in
             if uu____1684
             then
               let uu___105_1685 = goal in
               let uu____1686 =
                 let uu____1687 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1687 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___105_1685.witness);
                 goal_ty = uu____1686
               }
             else
               (let uu___106_1689 = goal in
                let uu____1690 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___106_1689.witness);
                  goal_ty = uu____1690
                }) in
           bind dismiss (fun uu____1691  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1698 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1698 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1710 =
                 let uu____1711 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1712 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1711 uu____1712 in
               fail uu____1710
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1725 = revert_all_hd xs1 in
        bind uu____1725 (fun uu____1727  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1731 =
      let uu____1732 = FStar_Syntax_Subst.compress x in
      uu____1732.FStar_Syntax_Syntax.n in
    match uu____1731 with
    | FStar_Syntax_Syntax.Tm_name uu____1735 -> true
    | uu____1736 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1740 =
      let uu____1741 = FStar_Syntax_Subst.compress x in
      uu____1741.FStar_Syntax_Syntax.n in
    match uu____1740 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1745 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun t  ->
    let uu____1757 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1757 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____1769)::(rhs,uu____1771)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____1797 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____1797 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____1869 =
               let uu____1877 = as_name x in (uu____1877, e, rhs) in
             Some uu____1869
         | uu____1889 -> None)
    | uu____1898 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____1921 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____1930 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____1930
           then
             let uu____1932 =
               let uu___107_1933 = p in
               let uu____1934 =
                 let uu____1936 = conj_goals g1 g2 in uu____1936 :: rest in
               {
                 main_context = (uu___107_1933.main_context);
                 main_goal = (uu___107_1933.main_goal);
                 all_implicits = (uu___107_1933.all_implicits);
                 goals = uu____1934;
                 smt_goals = (uu___107_1933.smt_goals);
                 transaction = (uu___107_1933.transaction)
               } in
             set uu____1932
           else
             (let g1_binders =
                let uu____1939 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____1939
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____1941 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____1941
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____1942 =
                let uu____1943 = goal_to_string g1 in
                let uu____1944 = goal_to_string g2 in
                let uu____1945 =
                  let uu____1946 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____1946 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____1943 uu____1944 uu____1945 in
              fail uu____1942)
       | uu____1947 ->
           let goals =
             let uu____1950 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____1950 (FStar_String.concat "\n\t") in
           let uu____1956 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____1956)
let rec visit: Prims.unit tac -> Prims.unit tac =
  fun callback  ->
    let uu____1964 =
      let uu____1966 =
        with_cur_goal
          (fun goal  ->
             let uu____1969 =
               FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
             match uu____1969 with
             | None  ->
                 let uu____1972 =
                   let uu____1973 = FStar_Syntax_Subst.compress goal.goal_ty in
                   uu____1973.FStar_Syntax_Syntax.n in
                 (match uu____1972 with
                  | FStar_Syntax_Syntax.Tm_meta uu____1977 ->
                      let uu____1982 = visit callback in map_meta uu____1982
                  | uu____1984 ->
                      let uu____1985 =
                        FStar_All.pipe_left mlog
                          (fun uu____1990  ->
                             let uu____1991 =
                               FStar_Syntax_Print.term_to_string goal.goal_ty in
                             FStar_Util.print1
                               "Not a formula, split to smt %s\n" uu____1991) in
                      bind uu____1985 (fun uu____1992  -> smt))
             | Some (FStar_Syntax_Util.QEx uu____1993) ->
                 let uu____1997 =
                   FStar_All.pipe_left mlog
                     (fun uu____2002  ->
                        let uu____2003 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        FStar_Util.print1
                          "Not yet handled: exists\n\tGoal is %s\n"
                          uu____2003) in
                 bind uu____1997 (fun uu____2004  -> ret ())
             | Some (FStar_Syntax_Util.QAll (xs,uu____2006,uu____2007)) ->
                 bind intros
                   (fun binders  ->
                      let uu____2009 = visit callback in
                      let uu____2011 =
                        let uu____2013 =
                          let uu____2015 = FStar_List.map Prims.fst binders in
                          revert_all_hd uu____2015 in
                        bind uu____2013
                          (fun uu____2019  ->
                             with_cur_goal
                               (fun goal1  ->
                                  let uu____2021 =
                                    FStar_All.pipe_left mlog
                                      (fun uu____2026  ->
                                         let uu____2027 =
                                           goal_to_string goal1 in
                                         FStar_Util.print1
                                           "After reverting intros, goal is %s\n"
                                           uu____2027) in
                                  bind uu____2021 (fun uu____2028  -> ret ()))) in
                      seq uu____2009 uu____2011)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2030)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
                 let uu____2031 =
                   let uu____2033 = visit callback in seq split uu____2033 in
                 bind uu____2031 (fun uu____2035  -> merge_sub_goals)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2037)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
                 bind imp_intro
                   (fun h  ->
                      let uu____2039 = visit callback in
                      seq uu____2039 revert)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2042)) ->
                 or_else trivial smt) in
      or_else callback uu____1966 in
    focus_cur_goal uu____1964
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2046 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2050 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2054 -> false
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
        let uu____2071 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2071 } in
      let uu____2072 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2072
      }