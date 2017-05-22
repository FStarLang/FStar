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
      tacprint1 "\nState dump (%s):" msg;
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
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_449 = p in
            {
              main_context = (uu___84_449.main_context);
              main_goal = (uu___84_449.main_goal);
              all_implicits = (uu___84_449.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___84_449.smt_goals);
              transaction = (uu___84_449.transaction)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___85_458 = p in
            {
              main_context = (uu___85_458.main_context);
              main_goal = (uu___85_458.main_goal);
              all_implicits = (uu___85_458.all_implicits);
              goals = (uu___85_458.goals);
              smt_goals = (FStar_List.append p.smt_goals gs);
              transaction = (uu___85_458.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____464  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___86_471 = p in
            {
              main_context = (uu___86_471.main_context);
              main_goal = (uu___86_471.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___86_471.goals);
              smt_goals = (uu___86_471.smt_goals);
              transaction = (uu___86_471.transaction)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____481 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____481 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid
    | uu____493 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____498 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____498 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid
    | uu____510 -> false
let conj_goals: goal -> goal -> goal =
  fun g1  ->
    fun g2  ->
      let t1 = g1.goal_ty in
      let t2 = g2.goal_ty in
      let uu____520 = (is_true t1) || (is_false t2) in
      if uu____520
      then g2
      else
        (let uu____522 = (is_true t2) || (is_false t1) in
         if uu____522
         then g1
         else
           (let uu___87_524 = g1 in
            let uu____525 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___87_524.context);
              witness = (uu___87_524.witness);
              goal_ty = uu____525
            }))
let with_cur_goal f =
  bind get
    (fun p  ->
       match p.goals with | [] -> fail "No more goals" | hd1::tl1 -> f hd1)
let cur_goal: goal tac =
  mk_tac
    (fun ps  ->
       match ps.goals with
       | hd1::uu____550 -> Success (hd1, ps)
       | uu____552 -> Failed ("No goals left", ps))
let set_cur_goal: goal -> Prims.unit tac =
  fun g  ->
    mk_tac
      (fun ps  ->
         match ps.goals with
         | hd1::tl1 ->
             Success
               ((),
                 (let uu___88_564 = ps in
                  {
                    main_context = (uu___88_564.main_context);
                    main_goal = (uu___88_564.main_goal);
                    all_implicits = (uu___88_564.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___88_564.smt_goals);
                    transaction = (uu___88_564.transaction)
                  }))
         | uu____565 -> Failed ("No goals left", ps))
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
        let uu____590 = FStar_Syntax_Util.term_eq e1 t in
        if uu____590 then e2 else t
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
                 let uu____633 = FStar_TypeChecker_Rel.try_teq true env t1 t2 in
                 match uu____633 with
                 | None  -> false
                 | Some g1 -> FStar_TypeChecker_Rel.is_trivial g1 in
               if ok
               then
                 let goal_ty' = treplace env e1 e2 g.goal_ty in
                 let uu____638 =
                   set_cur_goal
                     (let uu___89_640 = g in
                      {
                        context = (uu___89_640.context);
                        witness = (uu___89_640.witness);
                        goal_ty = goal_ty'
                      }) in
                 bind uu____638
                   (fun uu____641  ->
                      let uu____642 =
                        let uu____644 =
                          let uu____645 =
                            FStar_Syntax_Util.mk_eq2
                              FStar_Syntax_Syntax.U_zero t1 e1 e2 in
                          {
                            context = (g.context);
                            witness = None;
                            goal_ty = uu____645
                          } in
                        [uu____644] in
                      add_goals uu____642)
               else
                 (FStar_TypeChecker_Err.add_errors env
                    [("Ill-type rewriting requested",
                       (e1.FStar_Syntax_Syntax.pos))];
                  fail "grewrite: Ill-typed rewriting requested"))
let smt: Prims.unit tac =
  with_cur_goal
    (fun g  -> bind dismiss (fun uu____654  -> add_smt_goals [g]))
let focus_cur_goal f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___90_671 = p in
             {
               main_context = (uu___90_671.main_context);
               main_goal = (uu___90_671.main_goal);
               all_implicits = (uu___90_671.all_implicits);
               goals = [hd1];
               smt_goals = (uu___90_671.smt_goals);
               transaction = (uu___90_671.transaction)
             } in
           let uu____672 = set q in
           bind uu____672
             (fun uu____674  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___91_678 = q' in
                            {
                              main_context = (uu___91_678.main_context);
                              main_goal = (uu___91_678.main_goal);
                              all_implicits = (uu___91_678.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___91_678.smt_goals);
                              transaction = (uu___91_678.transaction)
                            } in
                          let uu____679 = set q2 in
                          bind uu____679 (fun uu____681  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret (None, None)
       | uu____721::[] -> bind f (fun a  -> ret ((Some a), None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____740  ->
                let uu____741 = add_goals [hd1] in
                bind uu____741
                  (fun uu____747  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____757  ->
                               match uu____757 with
                               | { main_context = uu____763;
                                   main_goal = uu____764;
                                   all_implicits = uu____765;
                                   goals = sub_goals_f;
                                   smt_goals = uu____767;
                                   transaction = uu____768;_} ->
                                   bind dismiss_all
                                     (fun uu____775  ->
                                        let uu____776 = add_goals tl1 in
                                        bind uu____776
                                          (fun uu____782  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____788 =
                                                    add_goals sub_goals_f in
                                                  bind uu____788
                                                    (fun uu____794  ->
                                                       ret
                                                         ((Some a), (Some b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____819 = t1.tac_f p in
       match uu____819 with | Failed uu____822 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____840 =
         let uu____843 =
           let uu____850 = map t in cur_goal_and_rest t uu____850 in
         bind uu____843
           (fun uu___79_860  ->
              match uu___79_860 with
              | (None ,None ) -> ret []
              | (None ,Some uu____873) -> failwith "impossible"
              | (Some hd1,None ) -> ret [hd1]
              | (Some hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____840 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal
        (fun g  ->
           let uu____909 =
             let uu___92_910 = g in
             let uu____911 = f g.goal_ty in
             {
               context = (uu___92_910.context);
               witness = (uu___92_910.witness);
               goal_ty = uu____911
             } in
           replace_cur uu____909) in
    let uu____912 = map aux in bind uu____912 (fun uu____916  -> ret ())
let map_meta t =
  with_cur_goal
    (fun g  ->
       let uu____929 =
         let uu____930 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____930.FStar_Syntax_Syntax.n in
       match uu____929 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____940 =
             replace_cur
               (let uu___93_942 = g in
                {
                  context = (uu___93_942.context);
                  witness = (uu___93_942.witness);
                  goal_ty = f
                }) in
           bind uu____940
             (fun uu____943  ->
                bind t
                  (fun a  ->
                     let uu____945 =
                       map_goal_term
                         (fun tm  ->
                            let uu____948 = is_true tm in
                            if uu____948
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____945 (fun uu____954  -> ret a)))
       | uu____955 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____968 =
        bind t1
          (fun uu____970  ->
             let uu____971 = map t2 in
             bind uu____971 (fun uu____975  -> ret ())) in
      focus_cur_goal uu____968
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal
    (fun goal  ->
       let uu____979 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____979 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____987  ->
                let uu____988 = add_goals [new_goal] in
                bind uu____988
                  (fun uu____990  ->
                     let uu____991 =
                       FStar_All.pipe_left mlog
                         (fun uu____996  ->
                            let uu____997 =
                              FStar_Syntax_Print.binders_to_string ", " bs in
                            FStar_Util.print1 "intros: %s\n" uu____997) in
                     bind uu____991 (fun uu____998  -> ret bs)))
       | uu____999 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____1002  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____1013 =
    let uu____1019 = FStar_Syntax_Syntax.as_arg p in [uu____1019] in
  FStar_Syntax_Util.mk_app sq uu____1013
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____1026 = FStar_Syntax_Util.head_and_args t in
    match uu____1026 with
    | (head1,args) ->
        let uu____1055 =
          let uu____1063 =
            let uu____1064 = FStar_Syntax_Util.un_uinst head1 in
            uu____1064.FStar_Syntax_Syntax.n in
          (uu____1063, args) in
        (match uu____1055 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____1077)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1097;
               FStar_Syntax_Syntax.index = uu____1098;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1100;
                   FStar_Syntax_Syntax.pos = uu____1101;
                   FStar_Syntax_Syntax.vars = uu____1102;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____1121 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal
    (fun goal  ->
       let uu____1133 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1133 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1138)::(rhs,uu____1140)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1168 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1168; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1169  ->
                let uu____1170 = add_goals [new_goal] in
                bind uu____1170
                  (fun uu____1172  ->
                     let uu____1173 =
                       FStar_All.pipe_left mlog
                         (fun uu____1178  ->
                            let uu____1179 =
                              FStar_Syntax_Print.bv_to_string name in
                            FStar_Util.print1 "imp_intro: %s\n" uu____1179) in
                     bind uu____1173
                       (fun uu____1180  ->
                          let uu____1181 = FStar_Syntax_Syntax.mk_binder name in
                          ret uu____1181)))
       | uu____1182 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1186 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1186 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1196  ->
                     match uu____1196 with
                     | (a,uu____1200) ->
                         let uu___94_1201 = goal in
                         {
                           context = (uu___94_1201.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1202  -> add_goals new_goals)
       | uu____1203 -> fail "Cannot split this goal; expected a conjunction")
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
         (let uu___95_1210 = goal in
          {
            context = (uu___95_1210.context);
            witness = (uu___95_1210.witness);
            goal_ty = t
          }))
let trivial: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Primops;
         FStar_TypeChecker_Normalize.UnfoldTac] in
       let t =
         FStar_TypeChecker_Normalize.normalize steps goal.context
           goal.goal_ty in
       let uu____1216 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1216 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid -> dismiss
       | uu____1229 ->
           let uu____1231 =
             let uu____1232 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format1 "Not a trivial goal: %s" uu____1232 in
           fail uu____1231)
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1242 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1242 with
           | (tm1,t,guard) ->
               let uu____1250 =
                 let uu____1251 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1251 in
               if uu____1250
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1254 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1254 with
                  | (bs,comp) ->
                      let uu____1269 =
                        FStar_List.fold_left
                          (fun uu____1286  ->
                             fun uu____1287  ->
                               match (uu____1286, uu____1287) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1336 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1336 with
                                    | (u,uu____1351,g_u) ->
                                        let uu____1359 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1359,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1269 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1391 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1407 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1437 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1391 with
                            | (pre,post) ->
                                let uu____1460 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1460 with
                                 | None  ->
                                     let uu____1463 =
                                       let uu____1464 =
                                         FStar_Syntax_Print.term_to_string
                                           post in
                                       let uu____1465 =
                                         FStar_Syntax_Print.term_to_string
                                           goal.goal_ty in
                                       FStar_Util.format2
                                         "apply_lemma: does not unify with goal: %s vs %s"
                                         uu____1464 uu____1465 in
                                     fail uu____1463
                                 | Some g ->
                                     let g1 =
                                       let uu____1468 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1468
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1504  ->
                                               match uu____1504 with
                                               | (uu____1511,uu____1512,uu____1513,tm2,uu____1515,uu____1516)
                                                   ->
                                                   let uu____1517 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1517 with
                                                    | (hd1,uu____1528) ->
                                                        let uu____1543 =
                                                          let uu____1544 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1544.FStar_Syntax_Syntax.n in
                                                        (match uu____1543
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1547 ->
                                                             true
                                                         | uu____1556 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____1560 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____1576  ->
                                                   match uu____1576 with
                                                   | (_msg,_env,_uvar,term,typ,uu____1588)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (Some term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___98_1589 = goal in
                                          {
                                            context = (uu___98_1589.context);
                                            witness = None;
                                            goal_ty = pre
                                          }) :: uu____1560 in
                                       let uu____1590 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1590
                                         (fun uu____1592  ->
                                            bind dismiss
                                              (fun uu____1593  ->
                                                 add_goals sub_goals))))))))
         with | uu____1596 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1606 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1606 with
           | (uu____1611,t,guard) ->
               let uu____1614 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1614
               then
                 (solve goal tm;
                  replace_cur
                    (let uu___101_1617 = goal in
                     {
                       context = (uu___101_1617.context);
                       witness = None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____1620 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1621 = FStar_Syntax_Print.term_to_string t in
                    let uu____1622 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1620
                      uu____1621 uu____1622 in
                  fail msg)
         with
         | e ->
             let uu____1626 =
               let uu____1627 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1627 in
             fail uu____1626)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal
      (fun goal  ->
         let uu____1634 =
           FStar_All.pipe_left mlog
             (fun uu____1639  ->
                let uu____1640 =
                  FStar_Syntax_Print.bv_to_string (Prims.fst h) in
                let uu____1641 =
                  FStar_Syntax_Print.term_to_string
                    (Prims.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1640
                  uu____1641) in
         bind uu____1634
           (fun uu____1642  ->
              let uu____1643 =
                let uu____1645 =
                  let uu____1646 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (Prims.fst h) in
                  FStar_All.pipe_left Prims.fst uu____1646 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1645 in
              match uu____1643 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1653::(x,uu____1655)::(e,uu____1657)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____1691 =
                    let uu____1692 = FStar_Syntax_Subst.compress x in
                    uu____1692.FStar_Syntax_Syntax.n in
                  (match uu____1691 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___102_1698 = goal in
                         let uu____1699 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___102_1698.context);
                           witness = (uu___102_1698.witness);
                           goal_ty = uu____1699
                         } in
                       replace_cur goal1
                   | uu____1702 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____1703 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1707 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1707 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1720 = FStar_Util.set_mem x fns in
           if uu____1720
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___103_1724 = goal in
                {
                  context = env';
                  witness = (uu___103_1724.witness);
                  goal_ty = (uu___103_1724.goal_ty)
                } in
              bind dismiss (fun uu____1725  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1732 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1732 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1747 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1747 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1761 = FStar_Util.set_mem x fvs in
             if uu____1761
             then
               let uu___104_1762 = goal in
               let uu____1763 =
                 let uu____1764 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1764 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___104_1762.witness);
                 goal_ty = uu____1763
               }
             else
               (let uu___105_1766 = goal in
                let uu____1767 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___105_1766.witness);
                  goal_ty = uu____1767
                }) in
           bind dismiss (fun uu____1768  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1775 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1775 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1787 =
                 let uu____1788 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1789 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1788 uu____1789 in
               fail uu____1787
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1802 = revert_all_hd xs1 in
        bind uu____1802 (fun uu____1804  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1808 =
      let uu____1809 = FStar_Syntax_Subst.compress x in
      uu____1809.FStar_Syntax_Syntax.n in
    match uu____1808 with
    | FStar_Syntax_Syntax.Tm_name uu____1812 -> true
    | uu____1813 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1817 =
      let uu____1818 = FStar_Syntax_Subst.compress x in
      uu____1818.FStar_Syntax_Syntax.n in
    match uu____1817 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1822 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun t  ->
    let uu____1834 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1834 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____1846)::(rhs,uu____1848)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____1874 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____1874 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____1946 =
               let uu____1954 = as_name x in (uu____1954, e, rhs) in
             Some uu____1946
         | uu____1966 -> None)
    | uu____1975 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____1998 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____2007 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____2007
           then
             let uu____2009 =
               let uu___106_2010 = p in
               let uu____2011 =
                 let uu____2013 = conj_goals g1 g2 in uu____2013 :: rest in
               {
                 main_context = (uu___106_2010.main_context);
                 main_goal = (uu___106_2010.main_goal);
                 all_implicits = (uu___106_2010.all_implicits);
                 goals = uu____2011;
                 smt_goals = (uu___106_2010.smt_goals);
                 transaction = (uu___106_2010.transaction)
               } in
             set uu____2009
           else
             (let g1_binders =
                let uu____2016 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____2016
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____2018 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____2018
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____2019 =
                let uu____2020 = goal_to_string g1 in
                let uu____2021 = goal_to_string g2 in
                let uu____2022 =
                  let uu____2023 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____2023 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____2020 uu____2021 uu____2022 in
              fail uu____2019)
       | uu____2024 ->
           let goals =
             let uu____2027 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____2027 (FStar_String.concat "\n\t") in
           let uu____2033 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____2033)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___107_2043 = g in
           {
             context = ctx';
             witness = (uu___107_2043.witness);
             goal_ty = (uu___107_2043.goal_ty)
           } in
         bind dismiss (fun uu____2044  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___108_2054 = g in
           {
             context = ctx';
             witness = (uu___108_2054.witness);
             goal_ty = (uu___108_2054.goal_ty)
           } in
         bind dismiss (fun uu____2055  -> add_goals [g']))
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
          let uu____2076 = FStar_Syntax_Subst.compress t in
          uu____2076.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2099 =
                let uu____2109 = ff hd1 in
                let uu____2110 =
                  FStar_List.map
                    (fun uu____2118  ->
                       match uu____2118 with
                       | (a,q) -> let uu____2125 = ff a in (uu____2125, q))
                    args in
                (uu____2109, uu____2110) in
              FStar_Syntax_Syntax.Tm_app uu____2099
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2154 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2154 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2160 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2160 t' in
                   let uu____2161 =
                     let uu____2176 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2176, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2161)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2195 -> tn in
        f env
          (let uu___109_2196 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___109_2196.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos =
               (uu___109_2196.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___109_2196.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2230 = f x in
      bind uu____2230
        (fun y  ->
           let uu____2234 = mapM f xs in
           bind uu____2234 (fun ys  -> ret (y :: ys)))
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
          let uu____2266 = FStar_Syntax_Subst.compress t in
          uu____2266.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2292 = ff hd1 in
              bind uu____2292
                (fun hd2  ->
                   let fa uu____2303 =
                     match uu____2303 with
                     | (a,q) ->
                         let uu____2311 = ff a in
                         bind uu____2311 (fun a1  -> ret (a1, q)) in
                   let uu____2318 = mapM fa args in
                   bind uu____2318
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2362 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2362 with
               | (bs1,t') ->
                   let uu____2368 =
                     let uu____2370 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2370 t' in
                   bind uu____2368
                     (fun t''  ->
                        let uu____2372 =
                          let uu____2373 =
                            let uu____2388 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2388, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2373 in
                        ret uu____2372))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2407 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___110_2409 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___110_2409.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___110_2409.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___110_2409.FStar_Syntax_Syntax.vars)
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
            let uu___111_2431 = env in
            {
              FStar_TypeChecker_Env.solver =
                (uu___111_2431.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___111_2431.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___111_2431.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___111_2431.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___111_2431.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___111_2431.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___111_2431.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___111_2431.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___111_2431.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp = false;
              FStar_TypeChecker_Env.effects =
                (uu___111_2431.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___111_2431.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___111_2431.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___111_2431.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___111_2431.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___111_2431.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___111_2431.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___111_2431.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___111_2431.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___111_2431.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___111_2431.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___111_2431.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___111_2431.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___111_2431.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___111_2431.FStar_TypeChecker_Env.proof_ns)
            } in
          let uu____2432 = FStar_TypeChecker_TcTerm.tc_term env1 t in
          match uu____2432 with
          | (t1,lcomp,g) ->
              let uu____2440 =
                (let uu____2441 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2441) ||
                  (let uu____2442 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2442) in
              if uu____2440
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2448 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env1 typ in
                 match uu____2448 with
                 | (ut,uvs,guard) ->
                     ((let uu____2466 = FStar_ST.read tacdbg in
                       if uu____2466
                       then
                         let uu____2469 =
                           FStar_Syntax_Print.term_to_string t1 in
                         let uu____2470 =
                           FStar_Syntax_Print.term_to_string ut in
                         FStar_Util.print2
                           "Pointwise_rec: making equality %s = %s\n"
                           uu____2469 uu____2470
                       else ());
                      (let g' =
                         let uu____2473 =
                           let uu____2474 =
                             FStar_TypeChecker_TcTerm.universe_of env1 typ in
                           FStar_Syntax_Util.mk_eq2 uu____2474 typ t1 ut in
                         {
                           context = env1;
                           witness = None;
                           goal_ty = uu____2473
                         } in
                       let uu____2475 = add_goals [g'] in
                       bind uu____2475
                         (fun uu____2477  ->
                            let uu____2478 =
                              bind tau (fun uu____2480  -> ret ut) in
                            focus_cur_goal uu____2478))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2489 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2489 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             ((let uu____2510 = FStar_ST.read tacdbg in
               if uu____2510
               then
                 let uu____2513 = FStar_Syntax_Print.term_to_string gt1 in
                 FStar_Util.print1 "Pointwise starting with %s\n" uu____2513
               else ());
              bind dismiss_all
                (fun uu____2515  ->
                   let uu____2516 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2516
                     (fun gt'  ->
                        (let uu____2520 = FStar_ST.read tacdbg in
                         if uu____2520
                         then
                           let uu____2523 =
                             FStar_Syntax_Print.term_to_string gt' in
                           FStar_Util.print1
                             "Pointwise seems to have succeded with %s\n"
                             uu____2523
                         else ());
                        (let uu____2525 = push_goals gs in
                         bind uu____2525
                           (fun uu____2527  ->
                              add_goals
                                [(let uu___112_2528 = g in
                                  {
                                    context = (uu___112_2528.context);
                                    witness = (uu___112_2528.witness);
                                    goal_ty = gt'
                                  })]))))))
let refl: Prims.unit tac =
  with_cur_goal
    (fun g  ->
       let uu____2531 = FStar_Syntax_Util.head_and_args' g.goal_ty in
       match uu____2531 with
       | (hd1,args) ->
           let uu____2552 =
             let uu____2560 =
               let uu____2561 = FStar_Syntax_Util.un_uinst hd1 in
               uu____2561.FStar_Syntax_Syntax.n in
             (uu____2560, args) in
           (match uu____2552 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,uu____2571::(l,uu____2573)::(r,uu____2575)::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid
                ->
                let uu____2609 =
                  FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                if uu____2609
                then dismiss
                else fail "refl: not a trivial equality"
            | (hd2,uu____2613) ->
                let uu____2624 =
                  let uu____2625 =
                    FStar_Syntax_Print.term_to_string
                      (let uu___113_2626 = g.goal_ty in
                       {
                         FStar_Syntax_Syntax.n = hd2;
                         FStar_Syntax_Syntax.tk =
                           (uu___113_2626.FStar_Syntax_Syntax.tk);
                         FStar_Syntax_Syntax.pos =
                           (uu___113_2626.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___113_2626.FStar_Syntax_Syntax.vars)
                       }) in
                  FStar_Util.format1 "refl: not an equality (%s)" uu____2625 in
                fail uu____2624))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2634 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2638 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2642 -> false
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
        let uu____2659 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2659 } in
      let uu____2660 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2660
      }