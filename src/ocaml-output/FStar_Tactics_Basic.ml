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
    let witness =
      match g.witness with
      | None  -> ""
      | Some t ->
          let uu____275 = FStar_Syntax_Print.term_to_string t in
          Prims.strcat uu____275 " : " in
    let uu____276 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format3 "%s |- %s%s" g_binders witness uu____276
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____286 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____286
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____296 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____296
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____309 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____309
let dump_goal ps goal =
  let uu____323 = goal_to_string goal in tacprint uu____323
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____333 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____333);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____339 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____339);
      FStar_List.iter (dump_goal ps) ps.smt_goals
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let log ps f =
  let uu____370 = FStar_ST.read tacdbg in if uu____370 then f () else ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____396 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____396 then dump_proofstate ps "TACTING FAILING" else ());
       Failed (msg, ps))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____403  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      match goal.witness with
      | None  -> ()
      | Some w ->
          let uu____411 =
            FStar_TypeChecker_Rel.teq_nosmt goal.context w solution in
          if uu____411
          then ()
          else
            (let uu____413 =
               let uu____414 =
                 let uu____415 = FStar_Syntax_Print.term_to_string solution in
                 let uu____416 = FStar_Syntax_Print.term_to_string w in
                 let uu____417 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 FStar_Util.format3 "%s does not solve %s : %s" uu____415
                   uu____416 uu____417 in
               Failure uu____414 in
             raise uu____413)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____420 =
         let uu___80_421 = p in
         let uu____422 = FStar_List.tl p.goals in
         {
           main_context = (uu___80_421.main_context);
           main_goal = (uu___80_421.main_goal);
           all_implicits = (uu___80_421.all_implicits);
           goals = uu____422;
           smt_goals = (uu___80_421.smt_goals);
           transaction = (uu___80_421.transaction)
         } in
       set uu____420)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___81_426 = p in
          {
            main_context = (uu___81_426.main_context);
            main_goal = (uu___81_426.main_goal);
            all_implicits = (uu___81_426.all_implicits);
            goals = [];
            smt_goals = (uu___81_426.smt_goals);
            transaction = (uu___81_426.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_435 = p in
            {
              main_context = (uu___82_435.main_context);
              main_goal = (uu___82_435.main_goal);
              all_implicits = (uu___82_435.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___82_435.smt_goals);
              transaction = (uu___82_435.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_444 = p in
            {
              main_context = (uu___83_444.main_context);
              main_goal = (uu___83_444.main_goal);
              all_implicits = (uu___83_444.all_implicits);
              goals = (uu___83_444.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___83_444.transaction)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_453 = p in
            {
              main_context = (uu___84_453.main_context);
              main_goal = (uu___84_453.main_goal);
              all_implicits = (uu___84_453.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___84_453.smt_goals);
              transaction = (uu___84_453.transaction)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___85_462 = p in
            {
              main_context = (uu___85_462.main_context);
              main_goal = (uu___85_462.main_goal);
              all_implicits = (uu___85_462.all_implicits);
              goals = (uu___85_462.goals);
              smt_goals = (FStar_List.append p.smt_goals gs);
              transaction = (uu___85_462.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____468  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___86_475 = p in
            {
              main_context = (uu___86_475.main_context);
              main_goal = (uu___86_475.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___86_475.goals);
              smt_goals = (uu___86_475.smt_goals);
              transaction = (uu___86_475.transaction)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____485 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____485 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid
    | uu____497 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____502 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____502 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid
    | uu____514 -> false
let conj_goals: goal -> goal -> goal =
  fun g1  ->
    fun g2  ->
      let t1 = g1.goal_ty in
      let t2 = g2.goal_ty in
      let uu____524 = (is_true t1) || (is_false t2) in
      if uu____524
      then g2
      else
        (let uu____526 = (is_true t2) || (is_false t1) in
         if uu____526
         then g1
         else
           (let uu___87_528 = g1 in
            let uu____529 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___87_528.context);
              witness = (uu___87_528.witness);
              goal_ty = uu____529
            }))
let with_cur_goal f =
  bind get
    (fun p  ->
       match p.goals with | [] -> fail "No more goals" | hd1::tl1 -> f hd1)
let cur_goal: goal tac =
  mk_tac
    (fun ps  ->
       match ps.goals with
       | hd1::uu____554 -> Success (hd1, ps)
       | uu____556 -> Failed ("No goals left", ps))
let set_cur_goal: goal -> Prims.unit tac =
  fun g  ->
    mk_tac
      (fun ps  ->
         match ps.goals with
         | hd1::tl1 ->
             Success
               ((),
                 (let uu___88_568 = ps in
                  {
                    main_context = (uu___88_568.main_context);
                    main_goal = (uu___88_568.main_goal);
                    all_implicits = (uu___88_568.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___88_568.smt_goals);
                    transaction = (uu___88_568.transaction)
                  }))
         | uu____569 -> Failed ("No goals left", ps))
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
        let uu____594 = FStar_Syntax_Util.term_eq e1 t in
        if uu____594 then e2 else t
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
                 let uu____637 = FStar_TypeChecker_Rel.try_teq true env t1 t2 in
                 match uu____637 with
                 | None  -> false
                 | Some g1 -> FStar_TypeChecker_Rel.is_trivial g1 in
               if ok
               then
                 let goal_ty' = treplace env e1 e2 g.goal_ty in
                 let uu____642 =
                   set_cur_goal
                     (let uu___89_644 = g in
                      {
                        context = (uu___89_644.context);
                        witness = (uu___89_644.witness);
                        goal_ty = goal_ty'
                      }) in
                 bind uu____642
                   (fun uu____645  ->
                      let uu____646 =
                        let uu____648 =
                          let uu____649 =
                            FStar_Syntax_Util.mk_eq2
                              FStar_Syntax_Syntax.U_zero t1 e1 e2 in
                          {
                            context = (g.context);
                            witness = None;
                            goal_ty = uu____649
                          } in
                        [uu____648] in
                      add_goals uu____646)
               else
                 (FStar_TypeChecker_Err.add_errors env
                    [("Ill-type rewriting requested",
                       (e1.FStar_Syntax_Syntax.pos))];
                  fail "grewrite: Ill-typed rewriting requested"))
let smt: Prims.unit tac =
  with_cur_goal
    (fun g  ->
       match g.witness with
       | None  -> bind dismiss (fun uu____659  -> add_smt_goals [g])
       | Some uu____660 ->
           fail "goal needs a witness: cannot dispatch to smt")
let focus_cur_goal f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___90_677 = p in
             {
               main_context = (uu___90_677.main_context);
               main_goal = (uu___90_677.main_goal);
               all_implicits = (uu___90_677.all_implicits);
               goals = [hd1];
               smt_goals = (uu___90_677.smt_goals);
               transaction = (uu___90_677.transaction)
             } in
           let uu____678 = set q in
           bind uu____678
             (fun uu____680  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___91_684 = q' in
                            {
                              main_context = (uu___91_684.main_context);
                              main_goal = (uu___91_684.main_goal);
                              all_implicits = (uu___91_684.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___91_684.smt_goals);
                              transaction = (uu___91_684.transaction)
                            } in
                          let uu____685 = set q2 in
                          bind uu____685 (fun uu____687  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret (None, None)
       | uu____727::[] -> bind f (fun a  -> ret ((Some a), None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____746  ->
                let uu____747 = add_goals [hd1] in
                bind uu____747
                  (fun uu____753  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____763  ->
                               match uu____763 with
                               | { main_context = uu____769;
                                   main_goal = uu____770;
                                   all_implicits = uu____771;
                                   goals = sub_goals_f;
                                   smt_goals = uu____773;
                                   transaction = uu____774;_} ->
                                   bind dismiss_all
                                     (fun uu____781  ->
                                        let uu____782 = add_goals tl1 in
                                        bind uu____782
                                          (fun uu____788  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____794 =
                                                    add_goals sub_goals_f in
                                                  bind uu____794
                                                    (fun uu____800  ->
                                                       ret
                                                         ((Some a), (Some b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____825 = t1.tac_f p in
       match uu____825 with | Failed uu____828 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____846 =
         let uu____849 =
           let uu____856 = map t in cur_goal_and_rest t uu____856 in
         bind uu____849
           (fun uu___79_866  ->
              match uu___79_866 with
              | (None ,None ) -> ret []
              | (None ,Some uu____879) -> failwith "impossible"
              | (Some hd1,None ) -> ret [hd1]
              | (Some hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____846 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal
        (fun g  ->
           let uu____915 =
             let uu___92_916 = g in
             let uu____917 = f g.goal_ty in
             {
               context = (uu___92_916.context);
               witness = (uu___92_916.witness);
               goal_ty = uu____917
             } in
           replace_cur uu____915) in
    let uu____918 = map aux in bind uu____918 (fun uu____922  -> ret ())
let map_meta t =
  with_cur_goal
    (fun g  ->
       let uu____935 =
         let uu____936 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____936.FStar_Syntax_Syntax.n in
       match uu____935 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____946 =
             replace_cur
               (let uu___93_948 = g in
                {
                  context = (uu___93_948.context);
                  witness = (uu___93_948.witness);
                  goal_ty = f
                }) in
           bind uu____946
             (fun uu____949  ->
                bind t
                  (fun a  ->
                     let uu____951 =
                       map_goal_term
                         (fun tm  ->
                            let uu____954 = is_true tm in
                            if uu____954
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____951 (fun uu____960  -> ret a)))
       | uu____961 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____974 =
        bind t1
          (fun uu____976  ->
             let uu____977 = map t2 in
             bind uu____977 (fun uu____981  -> ret ())) in
      focus_cur_goal uu____974
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal
    (fun goal  ->
       let uu____985 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____985 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____993  ->
                let uu____994 = add_goals [new_goal] in
                bind uu____994
                  (fun uu____996  ->
                     let uu____997 =
                       FStar_All.pipe_left mlog
                         (fun uu____1002  ->
                            let uu____1003 =
                              FStar_Syntax_Print.binders_to_string ", " bs in
                            FStar_Util.print1 "intros: %s\n" uu____1003) in
                     bind uu____997 (fun uu____1004  -> ret bs)))
       | uu____1005 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____1008  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____1019 =
    let uu____1025 = FStar_Syntax_Syntax.as_arg p in [uu____1025] in
  FStar_Syntax_Util.mk_app sq uu____1019
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____1032 = FStar_Syntax_Util.head_and_args t in
    match uu____1032 with
    | (head1,args) ->
        let uu____1061 =
          let uu____1069 =
            let uu____1070 = FStar_Syntax_Util.un_uinst head1 in
            uu____1070.FStar_Syntax_Syntax.n in
          (uu____1069, args) in
        (match uu____1061 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____1083)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1103;
               FStar_Syntax_Syntax.index = uu____1104;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1106;
                   FStar_Syntax_Syntax.pos = uu____1107;
                   FStar_Syntax_Syntax.vars = uu____1108;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____1127 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal
    (fun goal  ->
       let uu____1139 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1139 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1144)::(rhs,uu____1146)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1174 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1174; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1175  ->
                let uu____1176 = add_goals [new_goal] in
                bind uu____1176
                  (fun uu____1178  ->
                     let uu____1179 =
                       FStar_All.pipe_left mlog
                         (fun uu____1184  ->
                            let uu____1185 =
                              FStar_Syntax_Print.bv_to_string name in
                            FStar_Util.print1 "imp_intro: %s\n" uu____1185) in
                     bind uu____1179
                       (fun uu____1186  ->
                          let uu____1187 = FStar_Syntax_Syntax.mk_binder name in
                          ret uu____1187)))
       | uu____1188 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1192 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1192 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1202  ->
                     match uu____1202 with
                     | (a,uu____1206) ->
                         let uu___94_1207 = goal in
                         {
                           context = (uu___94_1207.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1208  -> add_goals new_goals)
       | uu____1209 -> fail "Cannot split this goal; expected a conjunction")
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
           let uu____1227 =
             let uu____1229 = FStar_List.map tr s in
             FStar_List.flatten uu____1229 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1227 in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___95_1234 = goal in
            {
              context = (uu___95_1234.context);
              witness = (uu___95_1234.witness);
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
       let uu____1246 = istrivial goal.context goal.goal_ty in
       if uu____1246
       then dismiss
       else
         (let uu____1249 =
            let uu____1250 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            FStar_Util.format1 "Not a trivial goal: %s" uu____1250 in
          fail uu____1249))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1260 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1260 with
           | (tm1,t,guard) ->
               let uu____1268 =
                 let uu____1269 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1269 in
               if uu____1268
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1272 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1272 with
                  | (bs,comp) ->
                      let uu____1287 =
                        FStar_List.fold_left
                          (fun uu____1304  ->
                             fun uu____1305  ->
                               match (uu____1304, uu____1305) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1354 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1354 with
                                    | (u,uu____1369,g_u) ->
                                        let uu____1377 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1377,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1287 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1409 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1425 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1455 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1409 with
                            | (pre,post) ->
                                let uu____1478 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1478 with
                                 | None  ->
                                     let uu____1481 =
                                       let uu____1482 =
                                         FStar_Syntax_Print.term_to_string
                                           post in
                                       let uu____1483 =
                                         FStar_Syntax_Print.term_to_string
                                           goal.goal_ty in
                                       FStar_Util.format2
                                         "apply_lemma: does not unify with goal: %s vs %s"
                                         uu____1482 uu____1483 in
                                     fail uu____1481
                                 | Some g ->
                                     let g1 =
                                       let uu____1486 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1486
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1522  ->
                                               match uu____1522 with
                                               | (uu____1529,uu____1530,uu____1531,tm2,uu____1533,uu____1534)
                                                   ->
                                                   let uu____1535 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1535 with
                                                    | (hd1,uu____1546) ->
                                                        let uu____1561 =
                                                          let uu____1562 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1562.FStar_Syntax_Syntax.n in
                                                        (match uu____1561
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1565 ->
                                                             true
                                                         | uu____1574 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let is_free_uvar uv t1 =
                                         let free_uvars =
                                           let uu____1593 =
                                             let uu____1597 =
                                               FStar_Syntax_Free.uvars t1 in
                                             FStar_Util.set_elements
                                               uu____1597 in
                                           FStar_List.map Prims.fst
                                             uu____1593 in
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
                                             let uu____1647 =
                                               FStar_Syntax_Util.head_and_args
                                                 t2 in
                                             (match uu____1647 with
                                              | (hd1,uu____1658) ->
                                                  (match hd1.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_uvar
                                                       (uv,uu____1674) ->
                                                       appears uv goals
                                                   | uu____1687 -> false)) in
                                       let sub_goals =
                                         FStar_All.pipe_right implicits1
                                           (FStar_List.map
                                              (fun uu____1704  ->
                                                 match uu____1704 with
                                                 | (_msg,_env,_uvar,term,typ,uu____1716)
                                                     ->
                                                     let uu____1717 =
                                                       FStar_TypeChecker_Normalize.normalize
                                                         [FStar_TypeChecker_Normalize.WHNF]
                                                         goal.context typ in
                                                     {
                                                       context =
                                                         (goal.context);
                                                       witness = (Some term);
                                                       goal_ty = uu____1717
                                                     })) in
                                       let rec filter' f xs =
                                         match xs with
                                         | [] -> []
                                         | x::xs1 ->
                                             let uu____1749 = f x xs1 in
                                             if uu____1749
                                             then
                                               let uu____1751 = filter' f xs1 in
                                               x :: uu____1751
                                             else filter' f xs1 in
                                       let sub_goals1 =
                                         filter'
                                           (fun g2  ->
                                              fun goals  ->
                                                let uu____1759 =
                                                  checkone g2.witness goals in
                                                Prims.op_Negation uu____1759)
                                           sub_goals in
                                       let sub_goals2 =
                                         let uu____1762 =
                                           istrivial goal.context pre in
                                         if uu____1762
                                         then sub_goals1
                                         else
                                           ((let uu___98_1765 = goal in
                                             {
                                               context =
                                                 (uu___98_1765.context);
                                               witness = None;
                                               goal_ty = pre
                                             }))
                                           :: sub_goals1 in
                                       let uu____1766 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1766
                                         (fun uu____1768  ->
                                            bind dismiss
                                              (fun uu____1769  ->
                                                 add_goals sub_goals2))))))))
         with | uu____1772 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1782 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1782 with
           | (uu____1787,t,guard) ->
               let uu____1790 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1790
               then (solve goal tm; dismiss)
               else
                 (let msg =
                    let uu____1795 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1796 = FStar_Syntax_Print.term_to_string t in
                    let uu____1797 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1795
                      uu____1796 uu____1797 in
                  fail msg)
         with
         | e ->
             let uu____1801 =
               let uu____1802 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1802 in
             fail uu____1801)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal
      (fun goal  ->
         let uu____1809 =
           FStar_All.pipe_left mlog
             (fun uu____1814  ->
                let uu____1815 =
                  FStar_Syntax_Print.bv_to_string (Prims.fst h) in
                let uu____1816 =
                  FStar_Syntax_Print.term_to_string
                    (Prims.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1815
                  uu____1816) in
         bind uu____1809
           (fun uu____1817  ->
              let uu____1818 =
                let uu____1820 =
                  let uu____1821 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (Prims.fst h) in
                  FStar_All.pipe_left Prims.fst uu____1821 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1820 in
              match uu____1818 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1828::(x,uu____1830)::(e,uu____1832)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____1866 =
                    let uu____1867 = FStar_Syntax_Subst.compress x in
                    uu____1867.FStar_Syntax_Syntax.n in
                  (match uu____1866 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___101_1873 = goal in
                         let uu____1874 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___101_1873.context);
                           witness = (uu___101_1873.witness);
                           goal_ty = uu____1874
                         } in
                       replace_cur goal1
                   | uu____1877 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____1878 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1882 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1882 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1895 = FStar_Util.set_mem x fns in
           if uu____1895
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___102_1899 = goal in
                {
                  context = env';
                  witness = (uu___102_1899.witness);
                  goal_ty = (uu___102_1899.goal_ty)
                } in
              bind dismiss (fun uu____1900  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1907 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1907 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1922 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1922 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1936 = FStar_Util.set_mem x fvs in
             if uu____1936
             then
               let uu___103_1937 = goal in
               let uu____1938 =
                 let uu____1939 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1939 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___103_1937.witness);
                 goal_ty = uu____1938
               }
             else
               (let uu___104_1941 = goal in
                let uu____1942 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___104_1941.witness);
                  goal_ty = uu____1942
                }) in
           bind dismiss (fun uu____1943  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1950 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1950 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1962 =
                 let uu____1963 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1964 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1963 uu____1964 in
               fail uu____1962
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1977 = revert_all_hd xs1 in
        bind uu____1977 (fun uu____1979  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1983 =
      let uu____1984 = FStar_Syntax_Subst.compress x in
      uu____1984.FStar_Syntax_Syntax.n in
    match uu____1983 with
    | FStar_Syntax_Syntax.Tm_name uu____1987 -> true
    | uu____1988 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1992 =
      let uu____1993 = FStar_Syntax_Subst.compress x in
      uu____1993.FStar_Syntax_Syntax.n in
    match uu____1992 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1997 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun t  ->
    let uu____2009 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____2009 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____2021)::(rhs,uu____2023)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____2049 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____2049 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____2121 =
               let uu____2129 = as_name x in (uu____2129, e, rhs) in
             Some uu____2121
         | uu____2141 -> None)
    | uu____2150 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____2173 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____2182 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____2182
           then
             let uu____2184 =
               let uu___105_2185 = p in
               let uu____2186 =
                 let uu____2188 = conj_goals g1 g2 in uu____2188 :: rest in
               {
                 main_context = (uu___105_2185.main_context);
                 main_goal = (uu___105_2185.main_goal);
                 all_implicits = (uu___105_2185.all_implicits);
                 goals = uu____2186;
                 smt_goals = (uu___105_2185.smt_goals);
                 transaction = (uu___105_2185.transaction)
               } in
             set uu____2184
           else
             (let g1_binders =
                let uu____2191 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____2191
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____2193 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____2193
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____2194 =
                let uu____2195 = goal_to_string g1 in
                let uu____2196 = goal_to_string g2 in
                let uu____2197 =
                  let uu____2198 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____2198 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____2195 uu____2196 uu____2197 in
              fail uu____2194)
       | uu____2199 ->
           let goals =
             let uu____2202 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____2202 (FStar_String.concat "\n\t") in
           let uu____2208 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____2208)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___106_2218 = g in
           {
             context = ctx';
             witness = (uu___106_2218.witness);
             goal_ty = (uu___106_2218.goal_ty)
           } in
         bind dismiss (fun uu____2219  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___107_2229 = g in
           {
             context = ctx';
             witness = (uu___107_2229.witness);
             goal_ty = (uu___107_2229.goal_ty)
           } in
         bind dismiss (fun uu____2230  -> add_goals [g']))
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
          let uu____2251 = FStar_Syntax_Subst.compress t in
          uu____2251.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2274 =
                let uu____2284 = ff hd1 in
                let uu____2285 =
                  FStar_List.map
                    (fun uu____2293  ->
                       match uu____2293 with
                       | (a,q) -> let uu____2300 = ff a in (uu____2300, q))
                    args in
                (uu____2284, uu____2285) in
              FStar_Syntax_Syntax.Tm_app uu____2274
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2329 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2329 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2335 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2335 t' in
                   let uu____2336 =
                     let uu____2351 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2351, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2336)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2370 -> tn in
        f env
          (let uu___108_2371 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___108_2371.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos =
               (uu___108_2371.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___108_2371.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2405 = f x in
      bind uu____2405
        (fun y  ->
           let uu____2409 = mapM f xs in
           bind uu____2409 (fun ys  -> ret (y :: ys)))
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
          let uu____2441 = FStar_Syntax_Subst.compress t in
          uu____2441.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2467 = ff hd1 in
              bind uu____2467
                (fun hd2  ->
                   let fa uu____2478 =
                     match uu____2478 with
                     | (a,q) ->
                         let uu____2486 = ff a in
                         bind uu____2486 (fun a1  -> ret (a1, q)) in
                   let uu____2493 = mapM fa args in
                   bind uu____2493
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2537 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2537 with
               | (bs1,t') ->
                   let uu____2543 =
                     let uu____2545 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2545 t' in
                   bind uu____2543
                     (fun t''  ->
                        let uu____2547 =
                          let uu____2548 =
                            let uu____2563 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2563, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2548 in
                        ret uu____2547))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2582 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___109_2584 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___109_2584.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___109_2584.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___109_2584.FStar_Syntax_Syntax.vars)
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
            let uu___110_2606 = env in
            {
              FStar_TypeChecker_Env.solver =
                (uu___110_2606.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___110_2606.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___110_2606.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___110_2606.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___110_2606.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___110_2606.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___110_2606.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___110_2606.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___110_2606.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp = false;
              FStar_TypeChecker_Env.effects =
                (uu___110_2606.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___110_2606.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___110_2606.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___110_2606.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___110_2606.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___110_2606.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___110_2606.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___110_2606.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___110_2606.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___110_2606.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___110_2606.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___110_2606.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___110_2606.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___110_2606.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___110_2606.FStar_TypeChecker_Env.proof_ns)
            } in
          let uu____2607 = FStar_TypeChecker_TcTerm.tc_term env1 t in
          match uu____2607 with
          | (t1,lcomp,g) ->
              let uu____2615 =
                (let uu____2616 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2616) ||
                  (let uu____2617 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2617) in
              if uu____2615
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2623 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env1 typ in
                 match uu____2623 with
                 | (ut,uvs,guard) ->
                     ((let uu____2641 = FStar_ST.read tacdbg in
                       if uu____2641
                       then
                         let uu____2644 =
                           FStar_Syntax_Print.term_to_string t1 in
                         let uu____2645 =
                           FStar_Syntax_Print.term_to_string ut in
                         FStar_Util.print2
                           "Pointwise_rec: making equality %s = %s\n"
                           uu____2644 uu____2645
                       else ());
                      (let g' =
                         let uu____2648 =
                           let uu____2649 =
                             FStar_TypeChecker_TcTerm.universe_of env1 typ in
                           FStar_Syntax_Util.mk_eq2 uu____2649 typ t1 ut in
                         {
                           context = env1;
                           witness = None;
                           goal_ty = uu____2648
                         } in
                       let uu____2650 = add_goals [g'] in
                       bind uu____2650
                         (fun uu____2652  ->
                            let uu____2653 =
                              bind tau
                                (fun uu____2655  ->
                                   let guard1 =
                                     let uu____2657 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env1 guard in
                                     FStar_All.pipe_right uu____2657
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env1 guard1;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.WHNF]
                                        env1 ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2653))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2668 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2668 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             ((let uu____2689 = FStar_ST.read tacdbg in
               if uu____2689
               then
                 let uu____2692 = FStar_Syntax_Print.term_to_string gt1 in
                 FStar_Util.print1 "Pointwise starting with %s\n" uu____2692
               else ());
              bind dismiss_all
                (fun uu____2694  ->
                   let uu____2695 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2695
                     (fun gt'  ->
                        (let uu____2699 = FStar_ST.read tacdbg in
                         if uu____2699
                         then
                           let uu____2702 =
                             FStar_Syntax_Print.term_to_string gt' in
                           FStar_Util.print1
                             "Pointwise seems to have succeded with %s\n"
                             uu____2702
                         else ());
                        (let uu____2704 = push_goals gs in
                         bind uu____2704
                           (fun uu____2706  ->
                              add_goals
                                [(let uu___111_2707 = g in
                                  {
                                    context = (uu___111_2707.context);
                                    witness = (uu___111_2707.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  with_cur_goal
    (fun g  ->
       let uu____2710 = FStar_Syntax_Util.head_and_args' g.goal_ty in
       match uu____2710 with
       | (hd1,args) ->
           let uu____2731 =
             let uu____2739 =
               let uu____2740 = FStar_Syntax_Util.un_uinst hd1 in
               uu____2740.FStar_Syntax_Syntax.n in
             (uu____2739, args) in
           (match uu____2731 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,uu____2750::(l,uu____2752)::(r,uu____2754)::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid
                ->
                let uu____2788 =
                  FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                if uu____2788
                then dismiss
                else fail "trefl: not a trivial equality"
            | (hd2,uu____2792) ->
                let uu____2803 =
                  let uu____2804 =
                    FStar_Syntax_Print.term_to_string
                      (let uu___112_2805 = g.goal_ty in
                       {
                         FStar_Syntax_Syntax.n = hd2;
                         FStar_Syntax_Syntax.tk =
                           (uu___112_2805.FStar_Syntax_Syntax.tk);
                         FStar_Syntax_Syntax.pos =
                           (uu___112_2805.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___112_2805.FStar_Syntax_Syntax.vars)
                       }) in
                  FStar_Util.format1 "trefl: not an equality (%s)" uu____2804 in
                fail uu____2803))
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___113_2816 = ps in
              {
                main_context = (uu___113_2816.main_context);
                main_goal = (uu___113_2816.main_goal);
                all_implicits = (uu___113_2816.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___113_2816.smt_goals);
                transaction = (uu___113_2816.transaction)
              }))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2820 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2824 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2828 -> false
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
        let uu____2845 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2845 } in
      let uu____2846 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2846
      }