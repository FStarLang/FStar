open Prims
type name = FStar_Syntax_Syntax.bv
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
type goal =
  {
  context: FStar_TypeChecker_Env.env;
  witness: FStar_Syntax_Syntax.term option;
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
  match projectee with | Success _0 -> true | uu____114 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success _0 -> _0
let uu___is_Failed projectee =
  match projectee with | Failed _0 -> true | uu____145 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed _0 -> _0
exception Failure of Prims.string
let uu___is_Failure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Failure uu____170 -> true | uu____171 -> false
let __proj__Failure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Failure uu____178 -> uu____178
type 'a tac = {
  tac_f: proofstate -> 'a result;}
let mk_tac f = { tac_f = f }
let run t p = t.tac_f p
let ret x = mk_tac (fun p  -> Success (x, p))
let bind t1 t2 =
  mk_tac
    (fun p  ->
       let uu____273 = run t1 p in
       match uu____273 with
       | Success (a,q) -> let uu____278 = t2 a in run uu____278 q
       | Failed (msg,q) -> Failed (msg, q))
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____286 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____286
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____287 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format2 "%s |- %s" g_binders uu____287
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____297 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____297
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____307 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____307
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____320 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____320
let dump_goal ps goal =
  let uu____334 = goal_to_string goal in tacprint uu____334
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint1 "State dump (%s):" msg;
      (let uu____343 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____343);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____349 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____349);
      FStar_List.iter (dump_goal ps) ps.smt_goals
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let log ps f =
  let uu____380 = FStar_ST.read tacdbg in if uu____380 then f () else ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg = mk_tac (fun p  -> Failed (msg, p))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____410  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      match goal.witness with
      | None  -> ()
      | Some w ->
          let uu____418 =
            FStar_TypeChecker_Rel.teq_nosmt goal.context w solution in
          if uu____418
          then ()
          else
            (let uu____420 =
               let uu____421 =
                 let uu____422 = FStar_Syntax_Print.term_to_string solution in
                 let uu____423 = FStar_Syntax_Print.term_to_string w in
                 let uu____424 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 FStar_Util.format3 "%s does not solve %s : %s" uu____422
                   uu____423 uu____424 in
               Failure uu____421 in
             raise uu____420)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____427 =
         let uu___79_428 = p in
         let uu____429 = FStar_List.tl p.goals in
         {
           main_context = (uu___79_428.main_context);
           main_goal = (uu___79_428.main_goal);
           all_implicits = (uu___79_428.all_implicits);
           goals = uu____429;
           smt_goals = (uu___79_428.smt_goals);
           transaction = (uu___79_428.transaction)
         } in
       set uu____427)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___80_433 = p in
          {
            main_context = (uu___80_433.main_context);
            main_goal = (uu___80_433.main_goal);
            all_implicits = (uu___80_433.all_implicits);
            goals = [];
            smt_goals = (uu___80_433.smt_goals);
            transaction = (uu___80_433.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_442 = p in
            {
              main_context = (uu___81_442.main_context);
              main_goal = (uu___81_442.main_goal);
              all_implicits = (uu___81_442.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___81_442.smt_goals);
              transaction = (uu___81_442.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_451 = p in
            {
              main_context = (uu___82_451.main_context);
              main_goal = (uu___82_451.main_goal);
              all_implicits = (uu___82_451.all_implicits);
              goals = (uu___82_451.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___82_451.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____457  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___83_464 = p in
            {
              main_context = (uu___83_464.main_context);
              main_goal = (uu___83_464.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___83_464.goals);
              smt_goals = (uu___83_464.smt_goals);
              transaction = (uu___83_464.transaction)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____474 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____474 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid
    | uu____486 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____491 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____491 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid
    | uu____503 -> false
let conj_goals: goal -> goal -> goal =
  fun g1  ->
    fun g2  ->
      let t1 = g1.goal_ty in
      let t2 = g2.goal_ty in
      let uu____513 = (is_true t1) || (is_false t2) in
      if uu____513
      then g2
      else
        (let uu____515 = (is_true t2) || (is_false t1) in
         if uu____515
         then g1
         else
           (let uu___84_517 = g1 in
            let uu____518 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___84_517.context);
              witness = (uu___84_517.witness);
              goal_ty = uu____518
            }))
let with_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with | [] -> fail "No more goals" | hd1::tl1 -> f hd1)
let cur_goal: goal tac =
  mk_tac
    (fun ps  ->
       match ps.goals with
       | hd1::uu____548 -> Success (hd1, ps)
       | uu____550 -> Failed ("No goals left", ps))
let set_cur_goal: goal -> Prims.unit tac =
  fun g  ->
    mk_tac
      (fun ps  ->
         match ps.goals with
         | hd1::tl1 ->
             Success
               ((),
                 (let uu___85_562 = ps in
                  {
                    main_context = (uu___85_562.main_context);
                    main_goal = (uu___85_562.main_goal);
                    all_implicits = (uu___85_562.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___85_562.smt_goals);
                    transaction = (uu___85_562.transaction)
                  }))
         | uu____563 -> Failed ("No goals left", ps))
let replace_point:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun e1  ->
    fun e2  ->
      fun t  ->
        let uu____574 = FStar_Syntax_Util.term_eq e1 t in
        if uu____574 then e2 else t
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
                     (let uu___86_622 = g in
                      {
                        context = (uu___86_622.context);
                        witness = (uu___86_622.witness);
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
  with_cur_goal "smt"
    (fun g  ->
       bind dismiss
         (fun uu____636  ->
            let uu____637 =
              add_goals
                [(let uu___87_639 = g in
                  {
                    context = (uu___87_639.context);
                    witness = (uu___87_639.witness);
                    goal_ty = FStar_Syntax_Util.t_true
                  })] in
            bind uu____637 (fun uu____640  -> add_smt_goals [g])))
let focus_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___88_662 = p in
             {
               main_context = (uu___88_662.main_context);
               main_goal = (uu___88_662.main_goal);
               all_implicits = (uu___88_662.all_implicits);
               goals = [hd1];
               smt_goals = (uu___88_662.smt_goals);
               transaction = (uu___88_662.transaction)
             } in
           let uu____663 = set q in
           bind uu____663
             (fun uu____665  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___89_669 = q' in
                            {
                              main_context = (uu___89_669.main_context);
                              main_goal = (uu___89_669.main_goal);
                              all_implicits = (uu___89_669.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___89_669.smt_goals);
                              transaction = (uu___89_669.transaction)
                            } in
                          let uu____670 = set q2 in
                          bind uu____670 (fun uu____672  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | uu____706::[] -> bind f (fun a  -> ret (a, None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____721  ->
                let uu____722 = add_goals [hd1] in
                bind uu____722
                  (fun uu____727  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____735  ->
                               match uu____735 with
                               | { main_context = uu____740;
                                   main_goal = uu____741;
                                   all_implicits = uu____742;
                                   goals = sub_goals_f;
                                   smt_goals = uu____744;
                                   transaction = uu____745;_} ->
                                   bind dismiss_all
                                     (fun uu____751  ->
                                        let uu____752 = add_goals tl1 in
                                        bind uu____752
                                          (fun uu____757  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____762 =
                                                    add_goals sub_goals_f in
                                                  bind uu____762
                                                    (fun uu____767  ->
                                                       ret (a, (Some b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____790 = t1.tac_f p in
       match uu____790 with | Failed uu____793 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____811 =
         let uu____814 =
           let uu____820 = map t in cur_goal_and_rest t uu____820 in
         bind uu____814
           (fun uu___78_829  ->
              match uu___78_829 with
              | (hd1,None ) -> ret [hd1]
              | (hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____811 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal "map_goal"
        (fun g  ->
           let uu____862 =
             let uu___90_863 = g in
             let uu____864 = f g.goal_ty in
             {
               context = (uu___90_863.context);
               witness = (uu___90_863.witness);
               goal_ty = uu____864
             } in
           replace_cur uu____862) in
    let uu____865 = map aux in bind uu____865 (fun uu____869  -> ret ())
let map_meta t =
  with_cur_goal "map_meta"
    (fun g  ->
       let uu____882 =
         let uu____883 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____883.FStar_Syntax_Syntax.n in
       match uu____882 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____893 =
             replace_cur
               (let uu___91_895 = g in
                {
                  context = (uu___91_895.context);
                  witness = (uu___91_895.witness);
                  goal_ty = f
                }) in
           bind uu____893
             (fun uu____896  ->
                bind t
                  (fun a  ->
                     let uu____898 =
                       map_goal_term
                         (fun tm  ->
                            let uu____901 = is_true tm in
                            if uu____901
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____898 (fun uu____907  -> ret a)))
       | uu____908 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____921 =
        bind t1
          (fun uu____923  ->
             let uu____924 = map t2 in
             bind uu____924 (fun uu____928  -> ret ())) in
      focus_cur_goal "seq" uu____921
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal "intros"
    (fun goal  ->
       let uu____932 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____932 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____940  ->
                let uu____941 = add_goals [new_goal] in
                bind uu____941
                  (fun uu____943  ->
                     let uu____944 =
                       FStar_All.pipe_left mlog
                         (fun uu____949  ->
                            let uu____950 =
                              FStar_Syntax_Print.binders_to_string ", " bs in
                            FStar_Util.print1 "intros: %s\n" uu____950) in
                     bind uu____944 (fun uu____951  -> ret bs)))
       | uu____952 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____955  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____966 = let uu____972 = FStar_Syntax_Syntax.as_arg p in [uu____972] in
  FStar_Syntax_Util.mk_app sq uu____966
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option
  =
  fun t  ->
    let uu____979 = FStar_Syntax_Util.head_and_args t in
    match uu____979 with
    | (head1,args) ->
        let uu____1008 =
          let uu____1016 =
            let uu____1017 = FStar_Syntax_Util.un_uinst head1 in
            uu____1017.FStar_Syntax_Syntax.n in
          (uu____1016, args) in
        (match uu____1008 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____1030)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1050;
               FStar_Syntax_Syntax.index = uu____1051;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1053;
                   FStar_Syntax_Syntax.pos = uu____1054;
                   FStar_Syntax_Syntax.vars = uu____1055;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____1074 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal "imp_intro"
    (fun goal  ->
       let uu____1086 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1086 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1091)::(rhs,uu____1093)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1121 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1121; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1122  ->
                let uu____1123 = add_goals [new_goal] in
                bind uu____1123
                  (fun uu____1125  ->
                     let uu____1126 =
                       FStar_All.pipe_left mlog
                         (fun uu____1131  ->
                            let uu____1132 =
                              FStar_Syntax_Print.bv_to_string name in
                            FStar_Util.print1 "imp_intro: %s\n" uu____1132) in
                     bind uu____1126
                       (fun uu____1133  ->
                          let uu____1134 = FStar_Syntax_Syntax.mk_binder name in
                          ret uu____1134)))
       | uu____1135 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal "split"
    (fun goal  ->
       let uu____1139 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1139 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1149  ->
                     match uu____1149 with
                     | (a,uu____1153) ->
                         let uu___92_1154 = goal in
                         {
                           context = (uu___92_1154.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1155  -> add_goals new_goals)
       | uu____1156 -> fail "Cannot split this goal; expected a conjunction")
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
       let uu____1163 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1163 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid ->
           bind dismiss
             (fun uu____1176  ->
                add_goals
                  [(let uu___93_1177 = goal in
                    {
                      context = (uu___93_1177.context);
                      witness = (uu___93_1177.witness);
                      goal_ty = t
                    })])
       | uu____1178 -> fail "Not a trivial goal")
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "apply_lemma"
      (fun goal  ->
         try
           let uu____1189 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1189 with
           | (tm1,t,guard) ->
               let uu____1197 =
                 let uu____1198 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1198 in
               if uu____1197
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1201 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1201 with
                  | (bs,comp) ->
                      let uu____1216 =
                        FStar_List.fold_left
                          (fun uu____1233  ->
                             fun uu____1234  ->
                               match (uu____1233, uu____1234) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1283 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1283 with
                                    | (u,uu____1298,g_u) ->
                                        let uu____1306 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1306,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1216 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1338 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1354 ->
                                 ((fst pre), (fst post))
                             | uu____1384 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1338 with
                            | (pre,post) ->
                                let uu____1407 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1407 with
                                 | None  ->
                                     fail
                                       "apply_lemma: does not unify with goal"
                                 | Some g ->
                                     let g1 =
                                       let uu____1412 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1412
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1446  ->
                                               match uu____1446 with
                                               | (uu____1453,uu____1454,uu____1455,tm2,uu____1457,uu____1458)
                                                   ->
                                                   let uu____1459 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1459 with
                                                    | (hd1,uu____1470) ->
                                                        let uu____1485 =
                                                          let uu____1486 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1486.FStar_Syntax_Syntax.n in
                                                        (match uu____1485
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1489 ->
                                                             true
                                                         | uu____1498 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____1502 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____1518  ->
                                                   match uu____1518 with
                                                   | (_msg,_env,_uvar,term,typ,uu____1530)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (Some term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___96_1531 = goal in
                                          {
                                            context = (uu___96_1531.context);
                                            witness = None;
                                            goal_ty = pre
                                          }) :: uu____1502 in
                                       let uu____1532 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1532
                                         (fun uu____1534  ->
                                            bind dismiss
                                              (fun uu____1535  ->
                                                 add_goals sub_goals))))))))
         with | uu____1538 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "exact"
      (fun goal  ->
         try
           let uu____1548 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1548 with
           | (uu____1553,t,guard) ->
               let uu____1556 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1556
               then
                 (solve goal tm;
                  replace_cur
                    (let uu___99_1559 = goal in
                     {
                       context = (uu___99_1559.context);
                       witness = None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____1562 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1563 = FStar_Syntax_Print.term_to_string t in
                    let uu____1564 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1562
                      uu____1563 uu____1564 in
                  fail msg)
         with
         | e ->
             let uu____1568 =
               let uu____1569 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1569 in
             fail uu____1568)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal "rewrite"
      (fun goal  ->
         let uu____1576 =
           FStar_All.pipe_left mlog
             (fun uu____1581  ->
                let uu____1582 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____1583 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1582
                  uu____1583) in
         bind uu____1576
           (fun uu____1584  ->
              let uu____1585 =
                let uu____1587 =
                  let uu____1588 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____1588 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1587 in
              match uu____1585 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1595::(x,uu____1597)::(e,uu____1599)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____1633 =
                    let uu____1634 = FStar_Syntax_Subst.compress x in
                    uu____1634.FStar_Syntax_Syntax.n in
                  (match uu____1633 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___100_1640 = goal in
                         let uu____1641 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___100_1640.context);
                           witness = (uu___100_1640.witness);
                           goal_ty = uu____1641
                         } in
                       replace_cur goal1
                   | uu____1644 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____1645 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal "clear"
    (fun goal  ->
       let uu____1649 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1649 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1662 = FStar_Util.set_mem x fns in
           if uu____1662
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___101_1666 = goal in
                {
                  context = env';
                  witness = (uu___101_1666.witness);
                  goal_ty = (uu___101_1666.goal_ty)
                } in
              bind dismiss (fun uu____1667  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "clear_hd"
      (fun goal  ->
         let uu____1674 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1674 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal "revert"
    (fun goal  ->
       let uu____1689 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1689 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1703 = FStar_Util.set_mem x fvs in
             if uu____1703
             then
               let uu___102_1704 = goal in
               let uu____1705 =
                 let uu____1706 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1706 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___102_1704.witness);
                 goal_ty = uu____1705
               }
             else
               (let uu___103_1708 = goal in
                let uu____1709 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___103_1708.witness);
                  goal_ty = uu____1709
                }) in
           bind dismiss (fun uu____1710  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "revert_hd"
      (fun goal  ->
         let uu____1717 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1717 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1729 =
                 let uu____1730 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1731 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1730 uu____1731 in
               fail uu____1729
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1744 = revert_all_hd xs1 in
        bind uu____1744 (fun uu____1746  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1750 =
      let uu____1751 = FStar_Syntax_Subst.compress x in
      uu____1751.FStar_Syntax_Syntax.n in
    match uu____1750 with
    | FStar_Syntax_Syntax.Tm_name uu____1754 -> true
    | uu____1755 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1759 =
      let uu____1760 = FStar_Syntax_Subst.compress x in
      uu____1760.FStar_Syntax_Syntax.n in
    match uu____1759 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1764 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) option
  =
  fun t  ->
    let uu____1776 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1776 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____1788)::(rhs,uu____1790)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____1816 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____1816 with
         | Some (FStar_Syntax_Util.BaseConn
             (eq1,uu____1827::(x,uu____1829)::(e,uu____1831)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____1865 =
               let uu____1873 = as_name x in (uu____1873, e, rhs) in
             Some uu____1865
         | Some (FStar_Syntax_Util.BaseConn
             (eq1,(x,uu____1887)::(e,uu____1889)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____1915 =
               let uu____1923 = as_name x in (uu____1923, e, rhs) in
             Some uu____1915
         | uu____1935 -> None)
    | uu____1944 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | [] -> ret a
            | uu____1966::[] -> ret a
            | uu____1967 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____1976 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____1976
           then
             let uu____1978 =
               let uu___104_1979 = p in
               let uu____1980 =
                 let uu____1982 = conj_goals g1 g2 in uu____1982 :: rest in
               {
                 main_context = (uu___104_1979.main_context);
                 main_goal = (uu___104_1979.main_goal);
                 all_implicits = (uu___104_1979.all_implicits);
                 goals = uu____1980;
                 smt_goals = (uu___104_1979.smt_goals);
                 transaction = (uu___104_1979.transaction)
               } in
             set uu____1978
           else
             (let g1_binders =
                let uu____1985 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____1985
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____1987 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____1987
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____1988 =
                let uu____1989 = goal_to_string g1 in
                let uu____1990 = goal_to_string g2 in
                let uu____1991 =
                  let uu____1992 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____1992 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____1989 uu____1990 uu____1991 in
              fail uu____1988)
       | uu____1993 ->
           let goals =
             let uu____1996 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____1996 (FStar_String.concat "\n\t") in
           let uu____2002 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____2002)
let rec visit: Prims.unit tac -> Prims.unit tac =
  fun callback  ->
    let uu____2010 =
      let uu____2012 =
        with_cur_goal "visit_strengthen_else"
          (fun goal  ->
             let uu____2015 =
               FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
             match uu____2015 with
             | None  ->
                 let uu____2018 =
                   let uu____2019 = FStar_Syntax_Subst.compress goal.goal_ty in
                   uu____2019.FStar_Syntax_Syntax.n in
                 (match uu____2018 with
                  | FStar_Syntax_Syntax.Tm_meta uu____2023 ->
                      let uu____2028 = visit callback in map_meta uu____2028
                  | uu____2030 ->
                      let uu____2031 =
                        FStar_All.pipe_left mlog
                          (fun uu____2036  ->
                             let uu____2037 =
                               FStar_Syntax_Print.term_to_string goal.goal_ty in
                             FStar_Util.print1
                               "Not a formula, split to smt %s\n" uu____2037) in
                      bind uu____2031 (fun uu____2038  -> smt))
             | Some (FStar_Syntax_Util.QEx uu____2039) ->
                 let uu____2043 =
                   FStar_All.pipe_left mlog
                     (fun uu____2048  ->
                        let uu____2049 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        FStar_Util.print1
                          "Not yet handled: exists\n\tGoal is %s\n"
                          uu____2049) in
                 bind uu____2043 (fun uu____2050  -> ret ())
             | Some (FStar_Syntax_Util.QAll (xs,uu____2052,uu____2053)) ->
                 bind intros
                   (fun binders  ->
                      let uu____2055 = visit callback in
                      let uu____2057 =
                        let uu____2059 =
                          let uu____2061 =
                            FStar_List.map FStar_Pervasives.fst binders in
                          revert_all_hd uu____2061 in
                        bind uu____2059
                          (fun uu____2065  ->
                             with_cur_goal "inner"
                               (fun goal1  ->
                                  let uu____2067 =
                                    FStar_All.pipe_left mlog
                                      (fun uu____2072  ->
                                         let uu____2073 =
                                           goal_to_string goal1 in
                                         FStar_Util.print1
                                           "After reverting intros, goal is %s\n"
                                           uu____2073) in
                                  bind uu____2067 (fun uu____2074  -> ret ()))) in
                      seq uu____2055 uu____2057)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2076)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
                 let uu____2077 =
                   let uu____2079 = visit callback in seq split uu____2079 in
                 bind uu____2077 (fun uu____2081  -> merge_sub_goals)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2083)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
                 bind imp_intro
                   (fun h  ->
                      let uu____2085 = visit callback in
                      seq uu____2085 revert)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2088)) ->
                 or_else trivial smt) in
      or_else callback uu____2012 in
    focus_cur_goal "visit_strengthen" uu____2010
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2092 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2096 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2100 -> false
let order_binder:
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder -> order =
  fun x  ->
    fun y  ->
      let n1 = FStar_Syntax_Syntax.order_bv (fst x) (fst y) in
      if n1 < (Prims.parse_int "0")
      then Lt
      else if n1 = (Prims.parse_int "0") then Eq else Gt
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> proofstate =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____2117 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2117 } in
      let uu____2118 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2118
      }