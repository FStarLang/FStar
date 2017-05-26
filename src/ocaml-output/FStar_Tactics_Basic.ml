open Prims
type name = FStar_Syntax_Syntax.bv
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
    let witness =
      match g.witness with
      | None  -> ""
      | Some t ->
          let uu____272 = FStar_Syntax_Print.term_to_string t in
          Prims.strcat uu____272 " : " in
    let uu____273 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format3 "%s |- %s%s" g_binders witness uu____273
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
let irrelevant: goal -> Prims.bool =
  fun g  -> match g.witness with | None  -> true | uu____310 -> false
let dump_goal ps goal =
  let uu____325 = goal_to_string goal in tacprint uu____325
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____335 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____335);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____341 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____341);
      FStar_List.iter (dump_goal ps) ps.smt_goals
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let tac_verb_dbg: Prims.bool option FStar_ST.ref = FStar_Util.mk_ref None
let rec log: proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun ps  ->
    fun f  ->
      let uu____371 = FStar_ST.read tac_verb_dbg in
      match uu____371 with
      | None  ->
          ((let uu____377 =
              let uu____379 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              Some uu____379 in
            FStar_ST.write tac_verb_dbg uu____377);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____405 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____405 then dump_proofstate ps "TACTING FAILING" else ());
       Failed (msg, ps))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____412  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      match goal.witness with
      | None  -> ()
      | Some w ->
          let uu____420 =
            FStar_TypeChecker_Rel.teq_nosmt goal.context w solution in
          if uu____420
          then ()
          else
            (let uu____422 =
               let uu____423 =
                 let uu____424 = FStar_Syntax_Print.term_to_string solution in
                 let uu____425 = FStar_Syntax_Print.term_to_string w in
                 let uu____426 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 FStar_Util.format3 "%s does not solve %s : %s" uu____424
                   uu____425 uu____426 in
               Failure uu____423 in
             raise uu____422)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____429 =
         let uu___80_430 = p in
         let uu____431 = FStar_List.tl p.goals in
         {
           main_context = (uu___80_430.main_context);
           main_goal = (uu___80_430.main_goal);
           all_implicits = (uu___80_430.all_implicits);
           goals = uu____431;
           smt_goals = (uu___80_430.smt_goals);
           transaction = (uu___80_430.transaction)
         } in
       set uu____429)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___81_435 = p in
          {
            main_context = (uu___81_435.main_context);
            main_goal = (uu___81_435.main_goal);
            all_implicits = (uu___81_435.all_implicits);
            goals = [];
            smt_goals = (uu___81_435.smt_goals);
            transaction = (uu___81_435.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_444 = p in
            {
              main_context = (uu___82_444.main_context);
              main_goal = (uu___82_444.main_goal);
              all_implicits = (uu___82_444.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___82_444.smt_goals);
              transaction = (uu___82_444.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_453 = p in
            {
              main_context = (uu___83_453.main_context);
              main_goal = (uu___83_453.main_goal);
              all_implicits = (uu___83_453.all_implicits);
              goals = (uu___83_453.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___83_453.transaction)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_462 = p in
            {
              main_context = (uu___84_462.main_context);
              main_goal = (uu___84_462.main_goal);
              all_implicits = (uu___84_462.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___84_462.smt_goals);
              transaction = (uu___84_462.transaction)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___85_471 = p in
            {
              main_context = (uu___85_471.main_context);
              main_goal = (uu___85_471.main_goal);
              all_implicits = (uu___85_471.all_implicits);
              goals = (uu___85_471.goals);
              smt_goals = (FStar_List.append p.smt_goals gs);
              transaction = (uu___85_471.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____477  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___86_484 = p in
            {
              main_context = (uu___86_484.main_context);
              main_goal = (uu___86_484.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___86_484.goals);
              smt_goals = (uu___86_484.smt_goals);
              transaction = (uu___86_484.transaction)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____494 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____494 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid
    | uu____506 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____511 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____511 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid
    | uu____523 -> false
let conj_goals: goal -> goal -> goal =
  fun g1  ->
    fun g2  ->
      let t1 = g1.goal_ty in
      let t2 = g2.goal_ty in
      let uu____533 = (is_true t1) || (is_false t2) in
      if uu____533
      then g2
      else
        (let uu____535 = (is_true t2) || (is_false t1) in
         if uu____535
         then g1
         else
           (let uu___87_537 = g1 in
            let uu____538 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___87_537.context);
              witness = (uu___87_537.witness);
              goal_ty = uu____538
            }))
let with_cur_goal f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> f hd1)
let cur_goal: goal tac =
  mk_tac
    (fun ps  ->
       match ps.goals with
       | hd1::uu____563 -> Success (hd1, ps)
       | uu____565 -> Failed ("No goals left", ps))
let set_cur_goal: goal -> Prims.unit tac =
  fun g  ->
    mk_tac
      (fun ps  ->
         match ps.goals with
         | hd1::tl1 ->
             Success
               ((),
                 (let uu___88_577 = ps in
                  {
                    main_context = (uu___88_577.main_context);
                    main_goal = (uu___88_577.main_goal);
                    all_implicits = (uu___88_577.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___88_577.smt_goals);
                    transaction = (uu___88_577.transaction)
                  }))
         | uu____578 -> Failed ("No goals left", ps))
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
        let uu____603 = FStar_Syntax_Util.term_eq e1 t in
        if uu____603 then e2 else t
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
                 let uu____646 = FStar_TypeChecker_Rel.try_teq true env t1 t2 in
                 match uu____646 with
                 | None  -> false
                 | Some g1 -> FStar_TypeChecker_Rel.is_trivial g1 in
               if ok
               then
                 let goal_ty' = treplace env e1 e2 g.goal_ty in
                 let uu____651 =
                   set_cur_goal
                     (let uu___89_653 = g in
                      {
                        context = (uu___89_653.context);
                        witness = (uu___89_653.witness);
                        goal_ty = goal_ty'
                      }) in
                 bind uu____651
                   (fun uu____654  ->
                      let uu____655 =
                        let uu____657 =
                          let uu____658 =
                            FStar_Syntax_Util.mk_eq2
                              FStar_Syntax_Syntax.U_zero t1 e1 e2 in
                          {
                            context = (g.context);
                            witness = None;
                            goal_ty = uu____658
                          } in
                        [uu____657] in
                      add_goals uu____655)
               else
                 (FStar_TypeChecker_Err.add_errors env
                    [("Ill-type rewriting requested",
                       (e1.FStar_Syntax_Syntax.pos))];
                  fail "grewrite: Ill-typed rewriting requested"))
let smt: Prims.unit tac =
  with_cur_goal
    (fun g  ->
       match g.witness with
       | None  -> bind dismiss (fun uu____668  -> add_smt_goals [g])
       | Some uu____669 ->
           fail "goal needs a witness: cannot dispatch to smt")
let focus_cur_goal f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (2)"
       | hd1::tl1 ->
           let q =
             let uu___90_686 = p in
             {
               main_context = (uu___90_686.main_context);
               main_goal = (uu___90_686.main_goal);
               all_implicits = (uu___90_686.all_implicits);
               goals = [hd1];
               smt_goals = (uu___90_686.smt_goals);
               transaction = (uu___90_686.transaction)
             } in
           let uu____687 = set q in
           bind uu____687
             (fun uu____689  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___91_693 = q' in
                            {
                              main_context = (uu___91_693.main_context);
                              main_goal = (uu___91_693.main_goal);
                              all_implicits = (uu___91_693.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___91_693.smt_goals);
                              transaction = (uu___91_693.transaction)
                            } in
                          let uu____694 = set q2 in
                          bind uu____694 (fun uu____696  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret (None, None)
       | uu____736::[] -> bind f (fun a  -> ret ((Some a), None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____755  ->
                let uu____756 = add_goals [hd1] in
                bind uu____756
                  (fun uu____762  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____772  ->
                               match uu____772 with
                               | { main_context = uu____778;
                                   main_goal = uu____779;
                                   all_implicits = uu____780;
                                   goals = sub_goals_f;
                                   smt_goals = uu____782;
                                   transaction = uu____783;_} ->
                                   bind dismiss_all
                                     (fun uu____790  ->
                                        let uu____791 = add_goals tl1 in
                                        bind uu____791
                                          (fun uu____797  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____803 =
                                                    add_goals sub_goals_f in
                                                  bind uu____803
                                                    (fun uu____809  ->
                                                       ret
                                                         ((Some a), (Some b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____834 = t1.tac_f p in
       match uu____834 with | Failed uu____837 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____855 =
         let uu____858 =
           let uu____865 = map t in cur_goal_and_rest t uu____865 in
         bind uu____858
           (fun uu___79_875  ->
              match uu___79_875 with
              | (None ,None ) -> ret []
              | (None ,Some uu____888) -> failwith "impossible"
              | (Some hd1,None ) -> ret [hd1]
              | (Some hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____855 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal
        (fun g  ->
           let uu____924 =
             let uu___92_925 = g in
             let uu____926 = f g.goal_ty in
             {
               context = (uu___92_925.context);
               witness = (uu___92_925.witness);
               goal_ty = uu____926
             } in
           replace_cur uu____924) in
    let uu____927 = map aux in bind uu____927 (fun uu____931  -> ret ())
let map_meta t =
  with_cur_goal
    (fun g  ->
       let uu____944 =
         let uu____945 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____945.FStar_Syntax_Syntax.n in
       match uu____944 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____955 =
             replace_cur
               (let uu___93_957 = g in
                {
                  context = (uu___93_957.context);
                  witness = (uu___93_957.witness);
                  goal_ty = f
                }) in
           bind uu____955
             (fun uu____958  ->
                bind t
                  (fun a  ->
                     let uu____960 =
                       map_goal_term
                         (fun tm  ->
                            let uu____963 = is_true tm in
                            if uu____963
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____960 (fun uu____969  -> ret a)))
       | uu____970 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____983 =
        bind t1
          (fun uu____985  ->
             let uu____986 = map t2 in
             bind uu____986 (fun uu____990  -> ret ())) in
      focus_cur_goal uu____983
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal
    (fun goal  ->
       let uu____994 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____994 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____1002  ->
                let uu____1003 = add_goals [new_goal] in
                bind uu____1003
                  (fun uu____1005  ->
                     let uu____1006 =
                       FStar_All.pipe_left mlog
                         (fun uu____1011  ->
                            let uu____1012 =
                              FStar_Syntax_Print.binders_to_string ", " bs in
                            FStar_Util.print1 "intros: %s\n" uu____1012) in
                     bind uu____1006 (fun uu____1013  -> ret bs)))
       | uu____1014 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____1017  -> ret ())
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal
    (fun goal  ->
       let uu____1020 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1020 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1025)::(rhs,uu____1027)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1055 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1055; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1056  ->
                let uu____1057 = add_goals [new_goal] in
                bind uu____1057
                  (fun uu____1059  ->
                     let uu____1060 =
                       FStar_All.pipe_left mlog
                         (fun uu____1065  ->
                            let uu____1066 =
                              FStar_Syntax_Print.bv_to_string name in
                            FStar_Util.print1 "imp_intro: %s\n" uu____1066) in
                     bind uu____1060
                       (fun uu____1067  ->
                          let uu____1068 = FStar_Syntax_Syntax.mk_binder name in
                          ret uu____1068)))
       | uu____1069 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1073 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1073 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1083  ->
                     match uu____1083 with
                     | (a,uu____1087) ->
                         let uu___94_1088 = goal in
                         {
                           context = (uu___94_1088.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1089  -> add_goals new_goals)
       | uu____1090 -> fail "Cannot split this goal; expected a conjunction")
let norm: FStar_Reflection_Data.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun goal  ->
         let tr s1 =
           match s1 with
           | FStar_Reflection_Data.Simpl  ->
               [FStar_TypeChecker_Normalize.Simplify]
           | FStar_Reflection_Data.WHNF  ->
               [FStar_TypeChecker_Normalize.WHNF]
           | FStar_Reflection_Data.Primops  ->
               [FStar_TypeChecker_Normalize.Primops] in
         let steps =
           let uu____1108 =
             let uu____1110 = FStar_List.map tr s in
             FStar_List.flatten uu____1110 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1108 in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___95_1115 = goal in
            {
              context = (uu___95_1115.context);
              witness = (uu___95_1115.witness);
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
       let uu____1127 = istrivial goal.context goal.goal_ty in
       if uu____1127
       then dismiss
       else
         (let uu____1130 =
            let uu____1131 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            FStar_Util.format1 "Not a trivial goal: %s" uu____1131 in
          fail uu____1130))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         let uu____1138 =
           (goal.context).FStar_TypeChecker_Env.type_of
             (let uu___96_1142 = goal.context in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___96_1142.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___96_1142.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___96_1142.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___96_1142.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___96_1142.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___96_1142.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ = None;
                FStar_TypeChecker_Env.sigtab =
                  (uu___96_1142.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___96_1142.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___96_1142.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___96_1142.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___96_1142.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs =
                  (uu___96_1142.FStar_TypeChecker_Env.letrecs);
                FStar_TypeChecker_Env.top_level =
                  (uu___96_1142.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___96_1142.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___96_1142.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___96_1142.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___96_1142.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___96_1142.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___96_1142.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.type_of =
                  (uu___96_1142.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___96_1142.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___96_1142.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qname_and_index =
                  (uu___96_1142.FStar_TypeChecker_Env.qname_and_index);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___96_1142.FStar_TypeChecker_Env.proof_ns)
              }) tm in
         match uu____1138 with
         | (tm1,t,guard) ->
             let uu____1147 =
               let uu____1149 =
                 let uu____1150 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1150 in
               if uu____1149 then fail "apply_lemma: not a lemma" else ret () in
             bind uu____1147
               (fun uu____1153  ->
                  let uu____1154 = FStar_Syntax_Util.arrow_formals_comp t in
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
                                 ((fst pre), (fst post))
                             | uu____1337 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1291 with
                            | (pre,post) ->
                                let uu____1360 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1360 with
                                 | None  ->
                                     let uu____1363 =
                                       let uu____1364 =
                                         FStar_Syntax_Print.term_to_string
                                           post in
                                       let uu____1365 =
                                         FStar_Syntax_Print.term_to_string
                                           goal.goal_ty in
                                       FStar_Util.format2
                                         "apply_lemma: does not unify with goal: %s vs %s"
                                         uu____1364 uu____1365 in
                                     fail uu____1363
                                 | Some g ->
                                     let g1 =
                                       let uu____1368 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1368
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1402  ->
                                               match uu____1402 with
                                               | (uu____1409,uu____1410,uu____1411,tm2,uu____1413,uu____1414)
                                                   ->
                                                   let uu____1415 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1415 with
                                                    | (hd1,uu____1426) ->
                                                        let uu____1441 =
                                                          let uu____1442 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1442.FStar_Syntax_Syntax.n in
                                                        (match uu____1441
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1445 ->
                                                             true
                                                         | uu____1454 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let is_free_uvar uv t1 =
                                         let free_uvars =
                                           let uu____1473 =
                                             let uu____1477 =
                                               FStar_Syntax_Free.uvars t1 in
                                             FStar_Util.set_elements
                                               uu____1477 in
                                           FStar_List.map
                                             FStar_Pervasives.fst uu____1473 in
                                         FStar_List.existsML
                                           (fun u  ->
                                              FStar_Unionfind.equivalent u uv)
                                           free_uvars in
                                       let appears uv goals =
                                         FStar_List.existsML
                                           (fun g'  ->
                                              is_free_uvar uv g'.goal_ty)
                                           goals in
                                       let checkone t1 goals =
                                         match t1 with
                                         | None  -> false
                                         | Some t2 ->
                                             let uu____1527 =
                                               FStar_Syntax_Util.head_and_args
                                                 t2 in
                                             (match uu____1527 with
                                              | (hd1,uu____1538) ->
                                                  (match hd1.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_uvar
                                                       (uv,uu____1554) ->
                                                       appears uv goals
                                                   | uu____1567 -> false)) in
                                       let sub_goals =
                                         FStar_All.pipe_right implicits1
                                           (FStar_List.map
                                              (fun uu____1584  ->
                                                 match uu____1584 with
                                                 | (_msg,_env,_uvar,term,typ,uu____1596)
                                                     ->
                                                     {
                                                       context =
                                                         (goal.context);
                                                       witness = (Some term);
                                                       goal_ty = typ
                                                     })) in
                                       let rec filter' f xs =
                                         match xs with
                                         | [] -> []
                                         | x::xs1 ->
                                             let uu____1628 = f x xs1 in
                                             if uu____1628
                                             then
                                               let uu____1630 = filter' f xs1 in
                                               x :: uu____1630
                                             else filter' f xs1 in
                                       let sub_goals1 =
                                         filter'
                                           (fun g2  ->
                                              fun goals  ->
                                                let uu____1638 =
                                                  checkone g2.witness goals in
                                                Prims.op_Negation uu____1638)
                                           sub_goals in
                                       let sub_goals2 =
                                         let uu____1641 =
                                           istrivial goal.context pre in
                                         if uu____1641
                                         then sub_goals1
                                         else
                                           ((let uu___97_1644 = goal in
                                             {
                                               context =
                                                 (uu___97_1644.context);
                                               witness = None;
                                               goal_ty = pre
                                             }))
                                           :: sub_goals1 in
                                       let uu____1645 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1645
                                         (fun uu____1647  ->
                                            bind dismiss
                                              (fun uu____1648  ->
                                                 add_goals sub_goals2)))))))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         let env =
           let uu___98_1656 = goal.context in
           {
             FStar_TypeChecker_Env.solver =
               (uu___98_1656.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___98_1656.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___98_1656.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___98_1656.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___98_1656.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___98_1656.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ = None;
             FStar_TypeChecker_Env.sigtab =
               (uu___98_1656.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___98_1656.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___98_1656.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___98_1656.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___98_1656.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___98_1656.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___98_1656.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___98_1656.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___98_1656.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___98_1656.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___98_1656.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___98_1656.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___98_1656.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.type_of =
               (uu___98_1656.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___98_1656.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___98_1656.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qname_and_index =
               (uu___98_1656.FStar_TypeChecker_Env.qname_and_index);
             FStar_TypeChecker_Env.proof_ns =
               (uu___98_1656.FStar_TypeChecker_Env.proof_ns)
           } in
         try
           let uu____1660 =
             (goal.context).FStar_TypeChecker_Env.type_of env tm in
           match uu____1660 with
           | (uu____1665,t,guard) ->
               let uu____1668 =
                 FStar_TypeChecker_Rel.teq_nosmt env t goal.goal_ty in
               if uu____1668
               then (solve goal tm; dismiss)
               else
                 (let msg =
                    let uu____1673 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1674 = FStar_Syntax_Print.term_to_string t in
                    let uu____1675 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1673
                      uu____1674 uu____1675 in
                  fail msg)
         with
         | e ->
             let uu____1679 =
               let uu____1680 = FStar_Syntax_Print.term_to_string tm in
               let uu____1681 = FStar_Syntax_Print.tag_of_term tm in
               FStar_Util.format2 "Term is not typeable: %s (%s)" uu____1680
                 uu____1681 in
             fail uu____1679)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal
      (fun goal  ->
         let uu____1688 =
           FStar_All.pipe_left mlog
             (fun uu____1693  ->
                let uu____1694 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____1695 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1694
                  uu____1695) in
         bind uu____1688
           (fun uu____1696  ->
              let uu____1697 =
                let uu____1699 =
                  let uu____1700 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____1700 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1699 in
              match uu____1697 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1707::(x,uu____1709)::(e,uu____1711)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____1745 =
                    let uu____1746 = FStar_Syntax_Subst.compress x in
                    uu____1746.FStar_Syntax_Syntax.n in
                  (match uu____1745 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___101_1752 = goal in
                         let uu____1753 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___101_1752.context);
                           witness = (uu___101_1752.witness);
                           goal_ty = uu____1753
                         } in
                       replace_cur goal1
                   | uu____1756 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____1757 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1761 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1761 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1774 = FStar_Util.set_mem x fns in
           if uu____1774
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___102_1778 = goal in
                {
                  context = env';
                  witness = (uu___102_1778.witness);
                  goal_ty = (uu___102_1778.goal_ty)
                } in
              bind dismiss (fun uu____1779  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1786 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1786 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1801 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1801 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1815 = FStar_Util.set_mem x fvs in
             if uu____1815
             then
               let uu___103_1816 = goal in
               let uu____1817 =
                 let uu____1818 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1818 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___103_1816.witness);
                 goal_ty = uu____1817
               }
             else
               (let uu___104_1820 = goal in
                let uu____1821 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___104_1820.witness);
                  goal_ty = uu____1821
                }) in
           bind dismiss (fun uu____1822  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1829 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1829 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1841 =
                 let uu____1842 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1843 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1842 uu____1843 in
               fail uu____1841
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1856 = revert_all_hd xs1 in
        bind uu____1856 (fun uu____1858  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1862 =
      let uu____1863 = FStar_Syntax_Subst.compress x in
      uu____1863.FStar_Syntax_Syntax.n in
    match uu____1862 with
    | FStar_Syntax_Syntax.Tm_name uu____1866 -> true
    | uu____1867 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1871 =
      let uu____1872 = FStar_Syntax_Subst.compress x in
      uu____1872.FStar_Syntax_Syntax.n in
    match uu____1871 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1876 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) option
  =
  fun t  ->
    let uu____1888 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1888 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____1900)::(rhs,uu____1902)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____1928 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____1928 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____2000 =
               let uu____2008 = as_name x in (uu____2008, e, rhs) in
             Some uu____2000
         | uu____2020 -> None)
    | uu____2029 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____2052 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____2061 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____2061
           then
             let uu____2063 =
               let uu___105_2064 = p in
               let uu____2065 =
                 let uu____2067 = conj_goals g1 g2 in uu____2067 :: rest in
               {
                 main_context = (uu___105_2064.main_context);
                 main_goal = (uu___105_2064.main_goal);
                 all_implicits = (uu___105_2064.all_implicits);
                 goals = uu____2065;
                 smt_goals = (uu___105_2064.smt_goals);
                 transaction = (uu___105_2064.transaction)
               } in
             set uu____2063
           else
             (let g1_binders =
                let uu____2070 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____2070
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____2072 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____2072
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____2073 =
                let uu____2074 = goal_to_string g1 in
                let uu____2075 = goal_to_string g2 in
                let uu____2076 =
                  let uu____2077 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____2077 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____2074 uu____2075 uu____2076 in
              fail uu____2073)
       | uu____2078 ->
           let goals =
             let uu____2081 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____2081 (FStar_String.concat "\n\t") in
           let uu____2087 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____2087)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___106_2097 = g in
           {
             context = ctx';
             witness = (uu___106_2097.witness);
             goal_ty = (uu___106_2097.goal_ty)
           } in
         bind dismiss (fun uu____2098  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___107_2108 = g in
           {
             context = ctx';
             witness = (uu___107_2108.witness);
             goal_ty = (uu___107_2108.goal_ty)
           } in
         bind dismiss (fun uu____2109  -> add_goals [g']))
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
          let uu____2130 = FStar_Syntax_Subst.compress t in
          uu____2130.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2153 =
                let uu____2163 = ff hd1 in
                let uu____2164 =
                  FStar_List.map
                    (fun uu____2172  ->
                       match uu____2172 with
                       | (a,q) -> let uu____2179 = ff a in (uu____2179, q))
                    args in
                (uu____2163, uu____2164) in
              FStar_Syntax_Syntax.Tm_app uu____2153
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2208 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2208 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2214 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2214 t' in
                   let uu____2215 =
                     let uu____2230 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2230, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2215)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2249 -> tn in
        f env
          (let uu___108_2250 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___108_2250.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos =
               (uu___108_2250.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___108_2250.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2284 = f x in
      bind uu____2284
        (fun y  ->
           let uu____2288 = mapM f xs in
           bind uu____2288 (fun ys  -> ret (y :: ys)))
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
          let uu____2320 = FStar_Syntax_Subst.compress t in
          uu____2320.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2346 = ff hd1 in
              bind uu____2346
                (fun hd2  ->
                   let fa uu____2357 =
                     match uu____2357 with
                     | (a,q) ->
                         let uu____2365 = ff a in
                         bind uu____2365 (fun a1  -> ret (a1, q)) in
                   let uu____2372 = mapM fa args in
                   bind uu____2372
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2416 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2416 with
               | (bs1,t') ->
                   let uu____2422 =
                     let uu____2424 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2424 t' in
                   bind uu____2422
                     (fun t''  ->
                        let uu____2426 =
                          let uu____2427 =
                            let uu____2442 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2442, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2427 in
                        ret uu____2426))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2461 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___109_2463 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___109_2463.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___109_2463.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___109_2463.FStar_Syntax_Syntax.vars)
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
          let env' =
            let uu___110_2485 = env in
            {
              FStar_TypeChecker_Env.solver =
                (uu___110_2485.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___110_2485.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___110_2485.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___110_2485.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___110_2485.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___110_2485.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ = None;
              FStar_TypeChecker_Env.sigtab =
                (uu___110_2485.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___110_2485.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp = false;
              FStar_TypeChecker_Env.effects =
                (uu___110_2485.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___110_2485.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___110_2485.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___110_2485.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___110_2485.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___110_2485.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___110_2485.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___110_2485.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___110_2485.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___110_2485.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___110_2485.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___110_2485.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___110_2485.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___110_2485.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___110_2485.FStar_TypeChecker_Env.proof_ns)
            } in
          let uu____2486 = FStar_TypeChecker_TcTerm.tc_term env' t in
          match uu____2486 with
          | (t1,lcomp,g) ->
              let uu____2494 =
                (let uu____2495 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2495) ||
                  (let uu____2496 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2496) in
              if uu____2494
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2502 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env typ in
                 match uu____2502 with
                 | (ut,uvs,guard) ->
                     (log ps
                        (fun uu____2520  ->
                           let uu____2521 =
                             FStar_Syntax_Print.term_to_string t1 in
                           let uu____2522 =
                             FStar_Syntax_Print.term_to_string ut in
                           FStar_Util.print2
                             "Pointwise_rec: making equality %s = %s\n"
                             uu____2521 uu____2522);
                      (let g' =
                         let uu____2524 =
                           let uu____2525 =
                             FStar_TypeChecker_TcTerm.universe_of env typ in
                           FStar_Syntax_Util.mk_eq2 uu____2525 typ t1 ut in
                         {
                           context = env;
                           witness = None;
                           goal_ty = uu____2524
                         } in
                       let uu____2526 = add_goals [g'] in
                       bind uu____2526
                         (fun uu____2528  ->
                            let uu____2529 =
                              bind tau
                                (fun uu____2531  ->
                                   let guard1 =
                                     let uu____2533 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env guard in
                                     FStar_All.pipe_right uu____2533
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env guard1;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.WHNF]
                                        env ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2529))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2544 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2544 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2565  ->
                   let uu____2566 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2566);
              bind dismiss_all
                (fun uu____2567  ->
                   let uu____2568 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2568
                     (fun gt'  ->
                        log ps
                          (fun uu____2572  ->
                             let uu____2573 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2573);
                        (let uu____2574 = push_goals gs in
                         bind uu____2574
                           (fun uu____2576  ->
                              add_goals
                                [(let uu___111_2577 = g in
                                  {
                                    context = (uu___111_2577.context);
                                    witness = (uu___111_2577.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  with_cur_goal
    (fun g  ->
       let uu____2580 = FStar_Syntax_Util.head_and_args' g.goal_ty in
       match uu____2580 with
       | (hd1,args) ->
           let uu____2601 =
             let uu____2609 =
               let uu____2610 = FStar_Syntax_Util.un_uinst hd1 in
               uu____2610.FStar_Syntax_Syntax.n in
             (uu____2609, args) in
           (match uu____2601 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,uu____2620::(l,uu____2622)::(r,uu____2624)::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid
                ->
                let uu____2658 =
                  FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                if uu____2658
                then dismiss
                else fail "trefl: not a trivial equality"
            | (hd2,uu____2662) ->
                let uu____2673 =
                  let uu____2674 =
                    FStar_Syntax_Print.term_to_string
                      (let uu___112_2675 = g.goal_ty in
                       {
                         FStar_Syntax_Syntax.n = hd2;
                         FStar_Syntax_Syntax.tk =
                           (uu___112_2675.FStar_Syntax_Syntax.tk);
                         FStar_Syntax_Syntax.pos =
                           (uu___112_2675.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___112_2675.FStar_Syntax_Syntax.vars)
                       }) in
                  FStar_Util.format1 "trefl: not an equality (%s)" uu____2674 in
                fail uu____2673))
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___113_2687 = ps in
              {
                main_context = (uu___113_2687.main_context);
                main_goal = (uu___113_2687.main_goal);
                all_implicits = (uu___113_2687.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___113_2687.smt_goals);
                transaction = (uu___113_2687.transaction)
              })
       | uu____2688 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___114_2696 = ps in
              {
                main_context = (uu___114_2696.main_context);
                main_goal = (uu___114_2696.main_goal);
                all_implicits = (uu___114_2696.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___114_2696.smt_goals);
                transaction = (uu___114_2696.transaction)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2700 -> fail "Not done!")
let unsquash: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac =
  fun t  ->
    with_cur_goal
      (fun g  ->
         let uu____2708 =
           let uu____2709 = irrelevant g in Prims.op_Negation uu____2709 in
         if uu____2708
         then fail "Goal is not irrelevant: cannot unsquash"
         else
           (let uu____2712 =
              (g.context).FStar_TypeChecker_Env.type_of
                (let uu___115_2716 = g.context in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___115_2716.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___115_2716.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___115_2716.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___115_2716.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___115_2716.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___115_2716.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ = None;
                   FStar_TypeChecker_Env.sigtab =
                     (uu___115_2716.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___115_2716.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___115_2716.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___115_2716.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___115_2716.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___115_2716.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___115_2716.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___115_2716.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___115_2716.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___115_2716.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___115_2716.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___115_2716.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___115_2716.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___115_2716.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___115_2716.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___115_2716.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___115_2716.FStar_TypeChecker_Env.qname_and_index);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___115_2716.FStar_TypeChecker_Env.proof_ns)
                 }) t in
            match uu____2712 with
            | (t1,typ,guard) ->
                let uu____2721 = FStar_Syntax_Util.head_and_args typ in
                (match uu____2721 with
                 | (hd1,args) ->
                     let uu____2748 =
                       let uu____2756 =
                         let uu____2757 = FStar_Syntax_Util.un_uinst hd1 in
                         uu____2757.FStar_Syntax_Syntax.n in
                       (uu____2756, args) in
                     (match uu____2748 with
                      | (FStar_Syntax_Syntax.Tm_fvar fv,(phi,uu____2768)::[])
                          when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Syntax_Const.squash_lid
                          ->
                          let v1 = FStar_Syntax_Syntax.new_bv None phi in
                          let g1 =
                            let uu___116_2788 = g in
                            let uu____2789 =
                              FStar_TypeChecker_Env.push_bv g.context v1 in
                            {
                              context = uu____2789;
                              witness = (uu___116_2788.witness);
                              goal_ty = (uu___116_2788.goal_ty)
                            } in
                          let uu____2790 = replace_cur g1 in
                          bind uu____2790
                            (fun uu____2792  ->
                               let uu____2793 =
                                 FStar_Syntax_Syntax.bv_to_name v1 in
                               ret uu____2793)
                      | uu____2794 ->
                          let uu____2802 =
                            let uu____2803 =
                              FStar_Syntax_Print.term_to_string typ in
                            FStar_Util.format1 "Not a squash: %s" uu____2803 in
                          fail uu____2802))))
let get_lemma: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac =
  fun t  ->
    with_cur_goal
      (fun g  ->
         let uu____2810 =
           (g.context).FStar_TypeChecker_Env.type_of
             (let uu___117_2814 = g.context in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___117_2814.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___117_2814.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___117_2814.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___117_2814.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___117_2814.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___117_2814.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ = None;
                FStar_TypeChecker_Env.sigtab =
                  (uu___117_2814.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___117_2814.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___117_2814.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___117_2814.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___117_2814.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs =
                  (uu___117_2814.FStar_TypeChecker_Env.letrecs);
                FStar_TypeChecker_Env.top_level =
                  (uu___117_2814.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___117_2814.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___117_2814.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___117_2814.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___117_2814.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___117_2814.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___117_2814.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.type_of =
                  (uu___117_2814.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___117_2814.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___117_2814.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qname_and_index =
                  (uu___117_2814.FStar_TypeChecker_Env.qname_and_index);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___117_2814.FStar_TypeChecker_Env.proof_ns)
              }) t in
         match uu____2810 with
         | (t1,typ,guard) ->
             let uu____2819 =
               let uu____2821 =
                 let uu____2822 = FStar_Syntax_Util.is_lemma typ in
                 Prims.op_Negation uu____2822 in
               if uu____2821
               then
                 let uu____2824 =
                   let uu____2825 = FStar_Syntax_Print.term_to_string typ in
                   FStar_Util.format1 "get_lemma: not a lemma (%s)"
                     uu____2825 in
                 fail uu____2824
               else ret () in
             bind uu____2819
               (fun uu____2827  ->
                  let uu____2828 = FStar_Syntax_Util.arrow_formals_comp typ in
                  match uu____2828 with
                  | (bs,comp) ->
                      let uu____2843 =
                        match bs with
                        | (x,uu____2847)::[] ->
                            let uu____2852 =
                              let uu____2853 =
                                FStar_Syntax_Subst.compress
                                  x.FStar_Syntax_Syntax.sort in
                              uu____2853.FStar_Syntax_Syntax.n in
                            (match uu____2852 with
                             | FStar_Syntax_Syntax.Tm_fvar fv when
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Syntax_Const.unit_lid
                                 ->
                                 let uu____2858 =
                                   let uu____2859 =
                                     FStar_Syntax_Free.names t1 in
                                   FStar_Util.set_mem x uu____2859 in
                                 if uu____2858
                                 then
                                   fail
                                     "get_lemma: unit arg is free in result type (???)"
                                 else ret ()
                             | uu____2863 ->
                                 let uu____2864 =
                                   let uu____2865 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort in
                                   FStar_Util.format1
                                     "get_lemma: lemma not unit-thunked (%s)"
                                     uu____2865 in
                                 fail uu____2864)
                        | uu____2866 ->
                            fail
                              "get_lemma: can only receive a lemma with a single unit argument" in
                      bind uu____2843
                        (fun uu____2870  ->
                           let uu____2871 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____2887 ->
                                 ((fst pre), (fst post))
                             | uu____2917 ->
                                 failwith "Impossible: not a lemma" in
                           match uu____2871 with
                           | (pre,post) ->
                               let v1 =
                                 let uu____2941 =
                                   FStar_Syntax_Util.mk_squash post in
                                 FStar_Syntax_Syntax.new_bv None uu____2941 in
                               let g' =
                                 let uu___118_2943 = g in
                                 let uu____2944 =
                                   FStar_TypeChecker_Env.push_bv g.context v1 in
                                 {
                                   context = uu____2944;
                                   witness = (uu___118_2943.witness);
                                   goal_ty = (uu___118_2943.goal_ty)
                                 } in
                               let uu____2945 = replace_cur g' in
                               bind uu____2945
                                 (fun uu____2947  ->
                                    let uu____2948 =
                                      FStar_Syntax_Syntax.bv_to_name v1 in
                                    ret uu____2948))))
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    with_cur_goal
      (fun g  ->
         let uu____2961 =
           (g.context).FStar_TypeChecker_Env.type_of
             (let uu___119_2965 = g.context in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___119_2965.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___119_2965.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___119_2965.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___119_2965.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___119_2965.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___119_2965.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ = None;
                FStar_TypeChecker_Env.sigtab =
                  (uu___119_2965.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___119_2965.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___119_2965.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___119_2965.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___119_2965.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs =
                  (uu___119_2965.FStar_TypeChecker_Env.letrecs);
                FStar_TypeChecker_Env.top_level =
                  (uu___119_2965.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___119_2965.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___119_2965.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___119_2965.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___119_2965.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___119_2965.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___119_2965.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.type_of =
                  (uu___119_2965.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___119_2965.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___119_2965.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qname_and_index =
                  (uu___119_2965.FStar_TypeChecker_Env.qname_and_index);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___119_2965.FStar_TypeChecker_Env.proof_ns)
              }) t in
         match uu____2961 with
         | (t1,typ,guard) ->
             let uu____2972 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2972 with
              | (hd1,args) ->
                  let uu____3001 =
                    let uu____3009 =
                      let uu____3010 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____3010.FStar_Syntax_Syntax.n in
                    (uu____3009, args) in
                  (match uu____3001 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____3023)::(q,uu____3025)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___120_3054 = g in
                         let uu____3055 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____3055;
                           witness = (uu___120_3054.witness);
                           goal_ty = (uu___120_3054.goal_ty)
                         } in
                       let g2 =
                         let uu___121_3057 = g in
                         let uu____3058 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____3058;
                           witness = (uu___121_3057.witness);
                           goal_ty = (uu___121_3057.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____3061  ->
                            let uu____3062 = add_goals [g1; g2] in
                            bind uu____3062
                              (fun uu____3066  ->
                                 let uu____3067 =
                                   let uu____3070 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____3071 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____3070, uu____3071) in
                                 ret uu____3067))
                   | uu____3074 ->
                       let uu____3082 =
                         let uu____3083 =
                           FStar_Syntax_Print.term_to_string typ in
                         FStar_Util.format1 "Not a disjunction: %s"
                           uu____3083 in
                       fail uu____3082)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____3089 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____3093 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____3097 -> false
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
        let uu____3114 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____3114 } in
      let uu____3115 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____3115
      }