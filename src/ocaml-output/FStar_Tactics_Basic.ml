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
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____330 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____330);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____336 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____336);
      FStar_List.iter (dump_goal ps) ps.smt_goals
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let log ps f =
  let uu____367 = FStar_ST.read tacdbg in if uu____367 then f () else ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____393 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____393 then dump_proofstate ps "TACTING FAILING" else ());
       Failed (msg, ps))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____400  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      match goal.witness with
      | None  -> ()
      | Some w ->
          let uu____408 =
            FStar_TypeChecker_Rel.teq_nosmt goal.context w solution in
          if uu____408
          then ()
          else
            (let uu____410 =
               let uu____411 =
                 let uu____412 = FStar_Syntax_Print.term_to_string solution in
                 let uu____413 = FStar_Syntax_Print.term_to_string w in
                 let uu____414 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 FStar_Util.format3 "%s does not solve %s : %s" uu____412
                   uu____413 uu____414 in
               Failure uu____411 in
             Prims.raise uu____410)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____417 =
         let uu___80_418 = p in
         let uu____419 = FStar_List.tl p.goals in
         {
           main_context = (uu___80_418.main_context);
           main_goal = (uu___80_418.main_goal);
           all_implicits = (uu___80_418.all_implicits);
           goals = uu____419;
           smt_goals = (uu___80_418.smt_goals);
           transaction = (uu___80_418.transaction)
         } in
       set uu____417)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___81_423 = p in
          {
            main_context = (uu___81_423.main_context);
            main_goal = (uu___81_423.main_goal);
            all_implicits = (uu___81_423.all_implicits);
            goals = [];
            smt_goals = (uu___81_423.smt_goals);
            transaction = (uu___81_423.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_432 = p in
            {
              main_context = (uu___82_432.main_context);
              main_goal = (uu___82_432.main_goal);
              all_implicits = (uu___82_432.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___82_432.smt_goals);
              transaction = (uu___82_432.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_441 = p in
            {
              main_context = (uu___83_441.main_context);
              main_goal = (uu___83_441.main_goal);
              all_implicits = (uu___83_441.all_implicits);
              goals = (uu___83_441.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___83_441.transaction)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_450 = p in
            {
              main_context = (uu___84_450.main_context);
              main_goal = (uu___84_450.main_goal);
              all_implicits = (uu___84_450.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___84_450.smt_goals);
              transaction = (uu___84_450.transaction)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___85_459 = p in
            {
              main_context = (uu___85_459.main_context);
              main_goal = (uu___85_459.main_goal);
              all_implicits = (uu___85_459.all_implicits);
              goals = (uu___85_459.goals);
              smt_goals = (FStar_List.append p.smt_goals gs);
              transaction = (uu___85_459.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____465  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___86_472 = p in
            {
              main_context = (uu___86_472.main_context);
              main_goal = (uu___86_472.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___86_472.goals);
              smt_goals = (uu___86_472.smt_goals);
              transaction = (uu___86_472.transaction)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____482 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____482 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid
    | uu____494 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____499 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____499 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid
    | uu____511 -> false
let conj_goals: goal -> goal -> goal =
  fun g1  ->
    fun g2  ->
      let t1 = g1.goal_ty in
      let t2 = g2.goal_ty in
      let uu____521 = (is_true t1) || (is_false t2) in
      if uu____521
      then g2
      else
        (let uu____523 = (is_true t2) || (is_false t1) in
         if uu____523
         then g1
         else
           (let uu___87_525 = g1 in
            let uu____526 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___87_525.context);
              witness = (uu___87_525.witness);
              goal_ty = uu____526
            }))
let with_cur_goal f =
  bind get
    (fun p  ->
       match p.goals with | [] -> fail "No more goals" | hd1::tl1 -> f hd1)
let cur_goal: goal tac =
  mk_tac
    (fun ps  ->
       match ps.goals with
       | hd1::uu____551 -> Success (hd1, ps)
       | uu____553 -> Failed ("No goals left", ps))
let set_cur_goal: goal -> Prims.unit tac =
  fun g  ->
    mk_tac
      (fun ps  ->
         match ps.goals with
         | hd1::tl1 ->
             Success
               ((),
                 (let uu___88_565 = ps in
                  {
                    main_context = (uu___88_565.main_context);
                    main_goal = (uu___88_565.main_goal);
                    all_implicits = (uu___88_565.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___88_565.smt_goals);
                    transaction = (uu___88_565.transaction)
                  }))
         | uu____566 -> Failed ("No goals left", ps))
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
        let uu____591 = FStar_Syntax_Util.term_eq e1 t in
        if uu____591 then e2 else t
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
                 let uu____634 = FStar_TypeChecker_Rel.try_teq true env t1 t2 in
                 match uu____634 with
                 | None  -> false
                 | Some g1 -> FStar_TypeChecker_Rel.is_trivial g1 in
               if ok
               then
                 let goal_ty' = treplace env e1 e2 g.goal_ty in
                 let uu____639 =
                   set_cur_goal
                     (let uu___89_641 = g in
                      {
                        context = (uu___89_641.context);
                        witness = (uu___89_641.witness);
                        goal_ty = goal_ty'
                      }) in
                 bind uu____639
                   (fun uu____642  ->
                      let uu____643 =
                        let uu____645 =
                          let uu____646 =
                            FStar_Syntax_Util.mk_eq2
                              FStar_Syntax_Syntax.U_zero t1 e1 e2 in
                          {
                            context = (g.context);
                            witness = None;
                            goal_ty = uu____646
                          } in
                        [uu____645] in
                      add_goals uu____643)
               else
                 (FStar_TypeChecker_Err.add_errors env
                    [("Ill-type rewriting requested",
                       (e1.FStar_Syntax_Syntax.pos))];
                  fail "grewrite: Ill-typed rewriting requested"))
let smt: Prims.unit tac =
  with_cur_goal
    (fun g  -> bind dismiss (fun uu____655  -> add_smt_goals [g]))
let focus_cur_goal f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___90_672 = p in
             {
               main_context = (uu___90_672.main_context);
               main_goal = (uu___90_672.main_goal);
               all_implicits = (uu___90_672.all_implicits);
               goals = [hd1];
               smt_goals = (uu___90_672.smt_goals);
               transaction = (uu___90_672.transaction)
             } in
           let uu____673 = set q in
           bind uu____673
             (fun uu____675  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___91_679 = q' in
                            {
                              main_context = (uu___91_679.main_context);
                              main_goal = (uu___91_679.main_goal);
                              all_implicits = (uu___91_679.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___91_679.smt_goals);
                              transaction = (uu___91_679.transaction)
                            } in
                          let uu____680 = set q2 in
                          bind uu____680 (fun uu____682  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret (None, None)
       | uu____722::[] -> bind f (fun a  -> ret ((Some a), None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____741  ->
                let uu____742 = add_goals [hd1] in
                bind uu____742
                  (fun uu____748  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____758  ->
                               match uu____758 with
                               | { main_context = uu____764;
                                   main_goal = uu____765;
                                   all_implicits = uu____766;
                                   goals = sub_goals_f;
                                   smt_goals = uu____768;
                                   transaction = uu____769;_} ->
                                   bind dismiss_all
                                     (fun uu____776  ->
                                        let uu____777 = add_goals tl1 in
                                        bind uu____777
                                          (fun uu____783  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____789 =
                                                    add_goals sub_goals_f in
                                                  bind uu____789
                                                    (fun uu____795  ->
                                                       ret
                                                         ((Some a), (Some b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____820 = t1.tac_f p in
       match uu____820 with | Failed uu____823 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____841 =
         let uu____844 =
           let uu____851 = map t in cur_goal_and_rest t uu____851 in
         bind uu____844
           (fun uu___79_861  ->
              match uu___79_861 with
              | (None ,None ) -> ret []
              | (None ,Some uu____874) -> failwith "impossible"
              | (Some hd1,None ) -> ret [hd1]
              | (Some hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____841 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal
        (fun g  ->
           let uu____910 =
             let uu___92_911 = g in
             let uu____912 = f g.goal_ty in
             {
               context = (uu___92_911.context);
               witness = (uu___92_911.witness);
               goal_ty = uu____912
             } in
           replace_cur uu____910) in
    let uu____913 = map aux in bind uu____913 (fun uu____917  -> ret ())
let map_meta t =
  with_cur_goal
    (fun g  ->
       let uu____930 =
         let uu____931 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____931.FStar_Syntax_Syntax.n in
       match uu____930 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____941 =
             replace_cur
               (let uu___93_943 = g in
                {
                  context = (uu___93_943.context);
                  witness = (uu___93_943.witness);
                  goal_ty = f
                }) in
           bind uu____941
             (fun uu____944  ->
                bind t
                  (fun a  ->
                     let uu____946 =
                       map_goal_term
                         (fun tm  ->
                            let uu____949 = is_true tm in
                            if uu____949
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____946 (fun uu____955  -> ret a)))
       | uu____956 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____969 =
        bind t1
          (fun uu____971  ->
             let uu____972 = map t2 in
             bind uu____972 (fun uu____976  -> ret ())) in
      focus_cur_goal uu____969
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal
    (fun goal  ->
       let uu____980 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____980 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____988  ->
                let uu____989 = add_goals [new_goal] in
                bind uu____989
                  (fun uu____991  ->
                     let uu____992 =
                       FStar_All.pipe_left mlog
                         (fun uu____997  ->
                            let uu____998 =
                              FStar_Syntax_Print.binders_to_string ", " bs in
                            FStar_Util.print1 "intros: %s\n" uu____998) in
                     bind uu____992 (fun uu____999  -> ret bs)))
       | uu____1000 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____1003  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____1014 =
    let uu____1020 = FStar_Syntax_Syntax.as_arg p in [uu____1020] in
  FStar_Syntax_Util.mk_app sq uu____1014
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____1027 = FStar_Syntax_Util.head_and_args t in
    match uu____1027 with
    | (head1,args) ->
        let uu____1056 =
          let uu____1064 =
            let uu____1065 = FStar_Syntax_Util.un_uinst head1 in
            uu____1065.FStar_Syntax_Syntax.n in
          (uu____1064, args) in
        (match uu____1056 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____1078)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1098;
               FStar_Syntax_Syntax.index = uu____1099;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1101;
                   FStar_Syntax_Syntax.pos = uu____1102;
                   FStar_Syntax_Syntax.vars = uu____1103;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____1122 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal
    (fun goal  ->
       let uu____1134 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1134 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1139)::(rhs,uu____1141)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1169 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1169; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1170  ->
                let uu____1171 = add_goals [new_goal] in
                bind uu____1171
                  (fun uu____1173  ->
                     let uu____1174 =
                       FStar_All.pipe_left mlog
                         (fun uu____1179  ->
                            let uu____1180 =
                              FStar_Syntax_Print.bv_to_string name in
                            FStar_Util.print1 "imp_intro: %s\n" uu____1180) in
                     bind uu____1174
                       (fun uu____1181  ->
                          let uu____1182 = FStar_Syntax_Syntax.mk_binder name in
                          ret uu____1182)))
       | uu____1183 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1187 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1187 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1197  ->
                     match uu____1197 with
                     | (a,uu____1201) ->
                         let uu___94_1202 = goal in
                         {
                           context = (uu___94_1202.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1203  -> add_goals new_goals)
       | uu____1204 -> fail "Cannot split this goal; expected a conjunction")
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
         (let uu___95_1211 = goal in
          {
            context = (uu___95_1211.context);
            witness = (uu___95_1211.witness);
            goal_ty = t
          }))
let istrivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.UnfoldTac] in
      let t1 = FStar_TypeChecker_Normalize.normalize steps e t in is_true t1
let trivial: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1223 = istrivial goal.context goal.goal_ty in
       if uu____1223
       then dismiss
       else
         (let uu____1226 =
            let uu____1227 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            FStar_Util.format1 "Not a trivial goal: %s" uu____1227 in
          fail uu____1226))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1237 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1237 with
           | (tm1,t,guard) ->
               let uu____1245 =
                 let uu____1246 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1246 in
               if uu____1245
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1249 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1249 with
                  | (bs,comp) ->
                      let uu____1264 =
                        FStar_List.fold_left
                          (fun uu____1281  ->
                             fun uu____1282  ->
                               match (uu____1281, uu____1282) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1331 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1331 with
                                    | (u,uu____1346,g_u) ->
                                        let uu____1354 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1354,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1264 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1386 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1402 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1432 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1386 with
                            | (pre,post) ->
                                let uu____1455 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1455 with
                                 | None  ->
                                     let uu____1458 =
                                       let uu____1459 =
                                         FStar_Syntax_Print.term_to_string
                                           post in
                                       let uu____1460 =
                                         FStar_Syntax_Print.term_to_string
                                           goal.goal_ty in
                                       FStar_Util.format2
                                         "apply_lemma: does not unify with goal: %s vs %s"
                                         uu____1459 uu____1460 in
                                     fail uu____1458
                                 | Some g ->
                                     let g1 =
                                       let uu____1463 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1463
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1499  ->
                                               match uu____1499 with
                                               | (uu____1506,uu____1507,uu____1508,tm2,uu____1510,uu____1511)
                                                   ->
                                                   let uu____1512 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1512 with
                                                    | (hd1,uu____1523) ->
                                                        let uu____1538 =
                                                          let uu____1539 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1539.FStar_Syntax_Syntax.n in
                                                        (match uu____1538
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1542 ->
                                                             true
                                                         | uu____1551 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         FStar_All.pipe_right implicits1
                                           (FStar_List.map
                                              (fun uu____1569  ->
                                                 match uu____1569 with
                                                 | (_msg,_env,_uvar,term,typ,uu____1581)
                                                     ->
                                                     {
                                                       context =
                                                         (goal.context);
                                                       witness = (Some term);
                                                       goal_ty = typ
                                                     })) in
                                       let sub_goals1 =
                                         let uu____1584 =
                                           istrivial goal.context pre in
                                         if uu____1584
                                         then sub_goals
                                         else
                                           ((let uu___98_1587 = goal in
                                             {
                                               context =
                                                 (uu___98_1587.context);
                                               witness = None;
                                               goal_ty = pre
                                             }))
                                           :: sub_goals in
                                       let uu____1588 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1588
                                         (fun uu____1590  ->
                                            bind dismiss
                                              (fun uu____1591  ->
                                                 add_goals sub_goals1))))))))
         with | uu____1594 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1604 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1604 with
           | (uu____1609,t,guard) ->
               let uu____1612 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1612
               then (solve goal tm; dismiss)
               else
                 (let msg =
                    let uu____1617 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1618 = FStar_Syntax_Print.term_to_string t in
                    let uu____1619 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1617
                      uu____1618 uu____1619 in
                  fail msg)
         with
         | e ->
             let uu____1623 =
               let uu____1624 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1624 in
             fail uu____1623)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal
      (fun goal  ->
         let uu____1631 =
           FStar_All.pipe_left mlog
             (fun uu____1636  ->
                let uu____1637 =
                  FStar_Syntax_Print.bv_to_string (Prims.fst h) in
                let uu____1638 =
                  FStar_Syntax_Print.term_to_string
                    (Prims.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1637
                  uu____1638) in
         bind uu____1631
           (fun uu____1639  ->
              let uu____1640 =
                let uu____1642 =
                  let uu____1643 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (Prims.fst h) in
                  FStar_All.pipe_left Prims.fst uu____1643 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1642 in
              match uu____1640 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1650::(x,uu____1652)::(e,uu____1654)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____1688 =
                    let uu____1689 = FStar_Syntax_Subst.compress x in
                    uu____1689.FStar_Syntax_Syntax.n in
                  (match uu____1688 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___101_1695 = goal in
                         let uu____1696 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___101_1695.context);
                           witness = (uu___101_1695.witness);
                           goal_ty = uu____1696
                         } in
                       replace_cur goal1
                   | uu____1699 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____1700 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1704 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1704 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1717 = FStar_Util.set_mem x fns in
           if uu____1717
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___102_1721 = goal in
                {
                  context = env';
                  witness = (uu___102_1721.witness);
                  goal_ty = (uu___102_1721.goal_ty)
                } in
              bind dismiss (fun uu____1722  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1729 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1729 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1744 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1744 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1758 = FStar_Util.set_mem x fvs in
             if uu____1758
             then
               let uu___103_1759 = goal in
               let uu____1760 =
                 let uu____1761 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1761 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___103_1759.witness);
                 goal_ty = uu____1760
               }
             else
               (let uu___104_1763 = goal in
                let uu____1764 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___104_1763.witness);
                  goal_ty = uu____1764
                }) in
           bind dismiss (fun uu____1765  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1772 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1772 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1784 =
                 let uu____1785 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1786 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1785 uu____1786 in
               fail uu____1784
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1799 = revert_all_hd xs1 in
        bind uu____1799 (fun uu____1801  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1805 =
      let uu____1806 = FStar_Syntax_Subst.compress x in
      uu____1806.FStar_Syntax_Syntax.n in
    match uu____1805 with
    | FStar_Syntax_Syntax.Tm_name uu____1809 -> true
    | uu____1810 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1814 =
      let uu____1815 = FStar_Syntax_Subst.compress x in
      uu____1815.FStar_Syntax_Syntax.n in
    match uu____1814 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1819 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun t  ->
    let uu____1831 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1831 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____1843)::(rhs,uu____1845)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____1871 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____1871 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____1943 =
               let uu____1951 = as_name x in (uu____1951, e, rhs) in
             Some uu____1943
         | uu____1963 -> None)
    | uu____1972 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____1995 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____2004 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____2004
           then
             let uu____2006 =
               let uu___105_2007 = p in
               let uu____2008 =
                 let uu____2010 = conj_goals g1 g2 in uu____2010 :: rest in
               {
                 main_context = (uu___105_2007.main_context);
                 main_goal = (uu___105_2007.main_goal);
                 all_implicits = (uu___105_2007.all_implicits);
                 goals = uu____2008;
                 smt_goals = (uu___105_2007.smt_goals);
                 transaction = (uu___105_2007.transaction)
               } in
             set uu____2006
           else
             (let g1_binders =
                let uu____2013 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____2013
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____2015 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____2015
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____2016 =
                let uu____2017 = goal_to_string g1 in
                let uu____2018 = goal_to_string g2 in
                let uu____2019 =
                  let uu____2020 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____2020 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____2017 uu____2018 uu____2019 in
              fail uu____2016)
       | uu____2021 ->
           let goals =
             let uu____2024 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____2024 (FStar_String.concat "\n\t") in
           let uu____2030 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____2030)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___106_2040 = g in
           {
             context = ctx';
             witness = (uu___106_2040.witness);
             goal_ty = (uu___106_2040.goal_ty)
           } in
         bind dismiss (fun uu____2041  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___107_2051 = g in
           {
             context = ctx';
             witness = (uu___107_2051.witness);
             goal_ty = (uu___107_2051.goal_ty)
           } in
         bind dismiss (fun uu____2052  -> add_goals [g']))
let rec bottom_fold_env:
  (FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
    ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2073 = FStar_Syntax_Subst.compress t in
          uu____2073.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2096 =
                let uu____2106 = ff hd1 in
                let uu____2107 =
                  FStar_List.map
                    (fun uu____2115  ->
                       match uu____2115 with
                       | (a,q) -> let uu____2122 = ff a in (uu____2122, q))
                    args in
                (uu____2106, uu____2107) in
              FStar_Syntax_Syntax.Tm_app uu____2096
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2151 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2151 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2157 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2157 t' in
                   let uu____2158 =
                     let uu____2173 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2173, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2158)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2192 -> tn in
        f env
          (let uu___108_2193 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___108_2193.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos =
               (uu___108_2193.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___108_2193.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2227 = f x in
      bind uu____2227
        (fun y  ->
           let uu____2231 = mapM f xs in
           bind uu____2231 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
    ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2263 = FStar_Syntax_Subst.compress t in
          uu____2263.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2289 = ff hd1 in
              bind uu____2289
                (fun hd2  ->
                   let fa uu____2300 =
                     match uu____2300 with
                     | (a,q) ->
                         let uu____2308 = ff a in
                         bind uu____2308 (fun a1  -> ret (a1, q)) in
                   let uu____2315 = mapM fa args in
                   bind uu____2315
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2359 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2359 with
               | (bs1,t') ->
                   let uu____2365 =
                     let uu____2367 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2367 t' in
                   bind uu____2365
                     (fun t''  ->
                        let uu____2369 =
                          let uu____2370 =
                            let uu____2385 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2385, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2370 in
                        ret uu____2369))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2404 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___109_2406 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___109_2406.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___109_2406.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___109_2406.FStar_Syntax_Syntax.vars)
                }))
let pointwise_rec:
  proofstate ->
    Prims.unit tac ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ps  ->
    fun tau  ->
      fun env  ->
        fun t  ->
          let env1 =
            let uu___110_2428 = env in
            {
              FStar_TypeChecker_Env.solver =
                (uu___110_2428.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___110_2428.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___110_2428.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___110_2428.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___110_2428.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___110_2428.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___110_2428.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___110_2428.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___110_2428.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp = false;
              FStar_TypeChecker_Env.effects =
                (uu___110_2428.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___110_2428.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___110_2428.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___110_2428.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___110_2428.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___110_2428.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___110_2428.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___110_2428.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___110_2428.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___110_2428.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___110_2428.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___110_2428.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___110_2428.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___110_2428.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___110_2428.FStar_TypeChecker_Env.proof_ns)
            } in
          let uu____2429 = FStar_TypeChecker_TcTerm.tc_term env1 t in
          match uu____2429 with
          | (t1,lcomp,g) ->
              let uu____2437 =
                (let uu____2438 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2438) ||
                  (let uu____2439 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2439) in
              if uu____2437
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2445 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env1 typ in
                 match uu____2445 with
                 | (ut,uvs,guard) ->
                     ((let uu____2463 = FStar_ST.read tacdbg in
                       if uu____2463
                       then
                         let uu____2466 =
                           FStar_Syntax_Print.term_to_string t1 in
                         let uu____2467 =
                           FStar_Syntax_Print.term_to_string ut in
                         FStar_Util.print2
                           "Pointwise_rec: making equality %s = %s\n"
                           uu____2466 uu____2467
                       else ());
                      (let g' =
                         let uu____2470 =
                           let uu____2471 =
                             FStar_TypeChecker_TcTerm.universe_of env1 typ in
                           FStar_Syntax_Util.mk_eq2 uu____2471 typ t1 ut in
                         {
                           context = env1;
                           witness = None;
                           goal_ty = uu____2470
                         } in
                       let uu____2472 = add_goals [g'] in
                       bind uu____2472
                         (fun uu____2474  ->
                            let uu____2475 =
                              bind tau
                                (fun uu____2477  ->
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env1 guard;
                                   ret ut) in
                            focus_cur_goal uu____2475))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2487 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2487 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             ((let uu____2508 = FStar_ST.read tacdbg in
               if uu____2508
               then
                 let uu____2511 = FStar_Syntax_Print.term_to_string gt1 in
                 FStar_Util.print1 "Pointwise starting with %s\n" uu____2511
               else ());
              bind dismiss_all
                (fun uu____2513  ->
                   let uu____2514 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2514
                     (fun gt'  ->
                        (let uu____2518 = FStar_ST.read tacdbg in
                         if uu____2518
                         then
                           let uu____2521 =
                             FStar_Syntax_Print.term_to_string gt' in
                           FStar_Util.print1
                             "Pointwise seems to have succeded with %s\n"
                             uu____2521
                         else ());
                        (let uu____2523 = push_goals gs in
                         bind uu____2523
                           (fun uu____2525  ->
                              add_goals
                                [(let uu___111_2526 = g in
                                  {
                                    context = (uu___111_2526.context);
                                    witness = (uu___111_2526.witness);
                                    goal_ty = gt'
                                  })]))))))
let refl: Prims.unit tac =
  with_cur_goal
    (fun g  ->
       let uu____2529 = FStar_Syntax_Util.head_and_args' g.goal_ty in
       match uu____2529 with
       | (hd1,args) ->
           let uu____2550 =
             let uu____2558 =
               let uu____2559 = FStar_Syntax_Util.un_uinst hd1 in
               uu____2559.FStar_Syntax_Syntax.n in
             (uu____2558, args) in
           (match uu____2550 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,uu____2569::(l,uu____2571)::(r,uu____2573)::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid
                ->
                let uu____2607 =
                  FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                if uu____2607
                then dismiss
                else fail "refl: not a trivial equality"
            | (hd2,uu____2611) ->
                let uu____2622 =
                  let uu____2623 =
                    FStar_Syntax_Print.term_to_string
                      (let uu___112_2624 = g.goal_ty in
                       {
                         FStar_Syntax_Syntax.n = hd2;
                         FStar_Syntax_Syntax.tk =
                           (uu___112_2624.FStar_Syntax_Syntax.tk);
                         FStar_Syntax_Syntax.pos =
                           (uu___112_2624.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___112_2624.FStar_Syntax_Syntax.vars)
                       }) in
                  FStar_Util.format1 "refl: not an equality (%s)" uu____2623 in
                fail uu____2622))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2632 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2636 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2640 -> false
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
        let uu____2657 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2657 } in
      let uu____2658 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2658
      }