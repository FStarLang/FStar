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
       if Prims.op_Negation t1.kernel then debug p t1.tac_name else ();
       (let uu____364 = t1.tac_f p in
        match uu____364 with
        | Success (a,q) ->
            let t21 = t2 a in
            (if Prims.op_Negation t21.kernel
             then debug q t21.tac_name
             else ();
             t21.tac_f q)
        | Failed (msg,q) ->
            (if Prims.op_Negation t1.kernel
             then
               (let uu____376 = FStar_Util.format1 "%s failed!" t1.tac_name in
                debug p uu____376)
             else ();
             Failed (msg, q))))
let get: proofstate tac = kernel_tac "get" (fun p  -> Success (p, p))
let fail msg =
  kernel_tac "fail"
    (fun p  -> FStar_Util.print1 ">>>>>%s\n" msg; Failed (msg, p))
let show: Prims.unit tac =
  kernel_tac "show" (fun p  -> debug p "debug"; Success ((), p))
let set: proofstate -> Prims.unit tac =
  fun p  -> kernel_tac "set" (fun uu____398  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      match goal.witness with
      | None  -> ()
      | Some w ->
          let uu____406 =
            FStar_TypeChecker_Rel.teq_nosmt goal.context w solution in
          if uu____406
          then ()
          else
            (let uu____408 =
               let uu____409 =
                 let uu____410 = FStar_Syntax_Print.term_to_string solution in
                 let uu____411 = FStar_Syntax_Print.term_to_string w in
                 let uu____412 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 FStar_Util.format3 "%s does not solve %s : %s" uu____410
                   uu____411 uu____412 in
               Failure uu____409 in
             Prims.raise uu____408)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____415 =
         let uu___78_416 = p in
         let uu____417 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_416.main_context);
           main_goal = (uu___78_416.main_goal);
           all_implicits = (uu___78_416.all_implicits);
           goals = uu____417;
           smt_goals = (uu___78_416.smt_goals);
           transaction = (uu___78_416.transaction)
         } in
       set uu____415)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_421 = p in
          {
            main_context = (uu___79_421.main_context);
            main_goal = (uu___79_421.main_goal);
            all_implicits = (uu___79_421.all_implicits);
            goals = [];
            smt_goals = (uu___79_421.smt_goals);
            transaction = (uu___79_421.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_430 = p in
            {
              main_context = (uu___80_430.main_context);
              main_goal = (uu___80_430.main_goal);
              all_implicits = (uu___80_430.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_430.smt_goals);
              transaction = (uu___80_430.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_439 = p in
            {
              main_context = (uu___81_439.main_context);
              main_goal = (uu___81_439.main_goal);
              all_implicits = (uu___81_439.all_implicits);
              goals = (uu___81_439.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___81_439.transaction)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____445  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___82_452 = p in
            {
              main_context = (uu___82_452.main_context);
              main_goal = (uu___82_452.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___82_452.goals);
              smt_goals = (uu___82_452.smt_goals);
              transaction = (uu___82_452.transaction)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____462 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____462 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid
    | uu____474 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____479 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____479 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid
    | uu____491 -> false
let conj_goals: goal -> goal -> goal =
  fun g1  ->
    fun g2  ->
      let t1 = g1.goal_ty in
      let t2 = g2.goal_ty in
      let uu____501 = (is_true t1) || (is_false t2) in
      if uu____501
      then g2
      else
        (let uu____503 = (is_true t2) || (is_false t1) in
         if uu____503
         then g1
         else
           (let uu___83_505 = g1 in
            let uu____506 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___83_505.context);
              witness = (uu___83_505.witness);
              goal_ty = uu____506
            }))
let with_cur_goal nm f =
  let uu____527 =
    bind get
      (fun p  ->
         match p.goals with | [] -> fail "No more goals" | hd1::tl1 -> f hd1) in
  name_tac nm uu____527
let cur_goal: goal tac =
  kernel_tac "cur_goal"
    (fun ps  ->
       match ps.goals with
       | hd1::uu____538 -> Success (hd1, ps)
       | uu____540 -> Failed ("No goals left", ps))
let set_cur_goal: goal -> Prims.unit tac =
  fun g  ->
    kernel_tac "set_cur_goal"
      (fun ps  ->
         match ps.goals with
         | hd1::tl1 ->
             Success
               ((),
                 (let uu___84_552 = ps in
                  {
                    main_context = (uu___84_552.main_context);
                    main_goal = (uu___84_552.main_goal);
                    all_implicits = (uu___84_552.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___84_552.smt_goals);
                    transaction = (uu___84_552.transaction)
                  }))
         | uu____553 -> Failed ("No goals left", ps))
let replace_point:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun e1  ->
    fun e2  ->
      fun t  ->
        let uu____564 = FStar_Syntax_Util.term_eq e1 t in
        if uu____564 then e2 else t
let rec replace_in_term:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun e1  ->
    fun e2  ->
      fun t  -> FStar_Syntax_Util.bottom_fold (replace_point e1 e2) t
let treplace env e1 e2 t =
  (let uu____598 = FStar_Syntax_Print.term_to_string e1 in
   let uu____599 = FStar_Syntax_Print.term_to_string e2 in
   let uu____600 = FStar_Syntax_Print.term_to_string t in
   FStar_Util.print3 "TAC replacing %s for %s in %s\n" uu____598 uu____599
     uu____600);
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
                 let uu____618 = FStar_TypeChecker_Rel.try_teq true env t1 t2 in
                 match uu____618 with
                 | None  -> false
                 | Some g1 -> FStar_TypeChecker_Rel.is_trivial g1 in
               if ok
               then
                 let goal_ty' = treplace env e1 e2 g.goal_ty in
                 let uu____623 =
                   set_cur_goal
                     (let uu___85_625 = g in
                      {
                        context = (uu___85_625.context);
                        witness = (uu___85_625.witness);
                        goal_ty = goal_ty'
                      }) in
                 bind uu____623
                   (fun uu____626  ->
                      let uu____627 =
                        let uu____629 =
                          let uu____630 =
                            FStar_Syntax_Util.mk_eq2
                              FStar_Syntax_Syntax.U_zero t1 e1 e2 in
                          {
                            context = (g.context);
                            witness = None;
                            goal_ty = uu____630
                          } in
                        [uu____629] in
                      add_goals uu____627)
               else
                 (FStar_TypeChecker_Err.add_errors env
                    [("Ill-type rewriting requested",
                       (e1.FStar_Syntax_Syntax.pos))];
                  fail "grewrite: Ill-typed rewriting requested"))
let smt: Prims.unit tac =
  with_cur_goal "smt"
    (fun g  ->
       bind dismiss
         (fun uu____639  ->
            let uu____640 =
              add_goals
                [(let uu___86_642 = g in
                  {
                    context = (uu___86_642.context);
                    witness = (uu___86_642.witness);
                    goal_ty = FStar_Syntax_Util.t_true
                  })] in
            bind uu____640 (fun uu____643  -> add_smt_goals [g])))
let focus_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___87_665 = p in
             {
               main_context = (uu___87_665.main_context);
               main_goal = (uu___87_665.main_goal);
               all_implicits = (uu___87_665.all_implicits);
               goals = [hd1];
               smt_goals = (uu___87_665.smt_goals);
               transaction = (uu___87_665.transaction)
             } in
           let uu____666 = set q in
           bind uu____666
             (fun uu____668  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___88_672 = q' in
                            {
                              main_context = (uu___88_672.main_context);
                              main_goal = (uu___88_672.main_goal);
                              all_implicits = (uu___88_672.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___88_672.smt_goals);
                              transaction = (uu___88_672.transaction)
                            } in
                          let uu____673 = set q2 in
                          bind uu____673 (fun uu____675  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | uu____709::[] -> bind f (fun a  -> ret (a, None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____724  ->
                let uu____725 = add_goals [hd1] in
                bind uu____725
                  (fun uu____730  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____738  ->
                               match uu____738 with
                               | { main_context = uu____743;
                                   main_goal = uu____744;
                                   all_implicits = uu____745;
                                   goals = sub_goals_f;
                                   smt_goals = uu____747;
                                   transaction = uu____748;_} ->
                                   bind dismiss_all
                                     (fun uu____754  ->
                                        let uu____755 = add_goals tl1 in
                                        bind uu____755
                                          (fun uu____760  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____765 =
                                                    add_goals sub_goals_f in
                                                  bind uu____765
                                                    (fun uu____770  ->
                                                       ret (a, (Some b)))))))))))
let or_else t1 t2 =
  kernel_tac "or_else"
    (fun p  ->
       (let uu____794 = FStar_Util.format1 "or_else: trying %s" t1.tac_name in
        debug p uu____794);
       (let uu____795 = t1.tac_f p in
        match uu____795 with
        | Failed uu____798 ->
            ((let uu____802 =
                FStar_Util.format2 "or_else: %s failed; trying %s"
                  t1.tac_name t2.tac_name in
              debug p uu____802);
             t2.tac_f p)
        | q -> q))
let rec map t =
  user_tac "map"
    (fun p  ->
       let uu____818 =
         let uu____821 =
           let uu____827 = map t in cur_goal_and_rest t uu____827 in
         bind uu____821
           (fun uu___76_836  ->
              match uu___76_836 with
              | (hd1,None ) -> ret [hd1]
              | (hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____818 p)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal "map_goal"
        (fun g  ->
           let uu____869 =
             let uu___89_870 = g in
             let uu____871 = f g.goal_ty in
             {
               context = (uu___89_870.context);
               witness = (uu___89_870.witness);
               goal_ty = uu____871
             } in
           replace_cur uu____869) in
    let uu____872 = map aux in bind uu____872 (fun uu____876  -> ret ())
let map_meta t =
  with_cur_goal "map_meta"
    (fun g  ->
       let uu____889 =
         let uu____890 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____890.FStar_Syntax_Syntax.n in
       match uu____889 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____900 =
             replace_cur
               (let uu___90_902 = g in
                {
                  context = (uu___90_902.context);
                  witness = (uu___90_902.witness);
                  goal_ty = f
                }) in
           bind uu____900
             (fun uu____903  ->
                bind t
                  (fun a  ->
                     let uu____905 =
                       map_goal_term
                         (fun tm  ->
                            let uu____908 = is_true tm in
                            if uu____908
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____905 (fun uu____914  -> ret a)))
       | uu____915 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____928 =
        bind t1
          (fun uu____930  ->
             let uu____931 = map t2 in
             bind uu____931 (fun uu____935  -> ret ())) in
      focus_cur_goal "seq" uu____928
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal "intros"
    (fun goal  ->
       let uu____939 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____939 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____947  ->
                let uu____948 = add_goals [new_goal] in
                bind uu____948
                  (fun uu____950  ->
                     (let uu____952 =
                        FStar_Syntax_Print.binders_to_string ", " bs in
                      FStar_Util.print1 "intros: %s\n" uu____952);
                     ret bs))
       | uu____953 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____956  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____967 = let uu____973 = FStar_Syntax_Syntax.as_arg p in [uu____973] in
  FStar_Syntax_Util.mk_app sq uu____967
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____980 = FStar_Syntax_Util.head_and_args t in
    match uu____980 with
    | (head1,args) ->
        let uu____1009 =
          let uu____1017 =
            let uu____1018 = FStar_Syntax_Util.un_uinst head1 in
            uu____1018.FStar_Syntax_Syntax.n in
          (uu____1017, args) in
        (match uu____1009 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____1031)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1051;
               FStar_Syntax_Syntax.index = uu____1052;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1054;
                   FStar_Syntax_Syntax.pos = uu____1055;
                   FStar_Syntax_Syntax.vars = uu____1056;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____1075 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal "imp_intro"
    (fun goal  ->
       let uu____1087 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1087 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1092)::(rhs,uu____1094)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1122 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1122; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1123  ->
                let uu____1124 = add_goals [new_goal] in
                bind uu____1124
                  (fun uu____1126  ->
                     (let uu____1128 = FStar_Syntax_Print.bv_to_string name in
                      FStar_Util.print1 "imp_intro: %s\n" uu____1128);
                     (let uu____1129 = FStar_Syntax_Syntax.mk_binder name in
                      ret uu____1129)))
       | uu____1130 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal "split"
    (fun goal  ->
       let uu____1134 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1134 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1144  ->
                     match uu____1144 with
                     | (a,uu____1148) ->
                         let uu___91_1149 = goal in
                         {
                           context = (uu___91_1149.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss
             (fun uu____1150  ->
                let uu____1151 = add_goals new_goals in
                bind uu____1151 (fun uu____1153  -> show))
       | uu____1154 -> fail "Cannot split this goal; expected a conjunction")
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
       let uu____1161 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1161 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid ->
           bind dismiss
             (fun uu____1174  ->
                add_goals
                  [(let uu___92_1175 = goal in
                    {
                      context = (uu___92_1175.context);
                      witness = (uu___92_1175.witness);
                      goal_ty = t
                    })])
       | uu____1176 -> fail "Not a trivial goal")
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "apply_lemma"
      (fun goal  ->
         try
           let uu____1187 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1187 with
           | (tm1,t,guard) ->
               let uu____1195 =
                 let uu____1196 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1196 in
               if uu____1195
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1199 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1199 with
                  | (bs,comp) ->
                      let uu____1214 =
                        FStar_List.fold_left
                          (fun uu____1231  ->
                             fun uu____1232  ->
                               match (uu____1231, uu____1232) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1281 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1281 with
                                    | (u,uu____1296,g_u) ->
                                        let uu____1304 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1304,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1214 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1336 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1352 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1382 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1336 with
                            | (pre,post) ->
                                let uu____1405 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1405 with
                                 | None  ->
                                     fail
                                       "apply_lemma: does not unify with goal"
                                 | Some g ->
                                     let g1 =
                                       let uu____1410 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1410
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
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
                                         (let uu___95_1531 = goal in
                                          {
                                            context = (uu___95_1531.context);
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
                    (let uu___98_1559 = goal in
                     {
                       context = (uu___98_1559.context);
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
         (let uu____1577 = FStar_Syntax_Print.bv_to_string (Prims.fst h) in
          let uu____1578 =
            FStar_Syntax_Print.term_to_string
              (Prims.fst h).FStar_Syntax_Syntax.sort in
          FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1577 uu____1578);
         (let uu____1579 =
            let uu____1581 =
              let uu____1582 =
                FStar_TypeChecker_Env.lookup_bv goal.context (Prims.fst h) in
              FStar_All.pipe_left Prims.fst uu____1582 in
            FStar_Syntax_Util.destruct_typ_as_formula uu____1581 in
          match uu____1579 with
          | Some (FStar_Syntax_Util.BaseConn
              (l,uu____1589::(x,uu____1591)::(e,uu____1593)::[])) when
              FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
              let uu____1627 =
                let uu____1628 = FStar_Syntax_Subst.compress x in
                uu____1628.FStar_Syntax_Syntax.n in
              (match uu____1627 with
               | FStar_Syntax_Syntax.Tm_name x1 ->
                   let goal1 =
                     let uu___99_1634 = goal in
                     let uu____1635 =
                       FStar_Syntax_Subst.subst
                         [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                     {
                       context = (uu___99_1634.context);
                       witness = (uu___99_1634.witness);
                       goal_ty = uu____1635
                     } in
                   replace_cur goal1
               | uu____1638 ->
                   fail
                     "Not an equality hypothesis with a variable on the LHS")
          | uu____1639 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal "clear"
    (fun goal  ->
       let uu____1643 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1643 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1656 = FStar_Util.set_mem x fns in
           if uu____1656
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___100_1660 = goal in
                {
                  context = env';
                  witness = (uu___100_1660.witness);
                  goal_ty = (uu___100_1660.goal_ty)
                } in
              bind dismiss (fun uu____1661  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "clear_hd"
      (fun goal  ->
         let uu____1668 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1668 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal "revert"
    (fun goal  ->
       let uu____1683 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1683 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____1697 = FStar_Util.set_mem x fvs in
             if uu____1697
             then
               let uu___101_1698 = goal in
               let uu____1699 =
                 let uu____1700 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____1700 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___101_1698.witness);
                 goal_ty = uu____1699
               }
             else
               (let uu___102_1702 = goal in
                let uu____1703 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___102_1702.witness);
                  goal_ty = uu____1703
                }) in
           bind dismiss (fun uu____1704  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "revert_hd"
      (fun goal  ->
         let uu____1711 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1711 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1723 =
                 let uu____1724 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1725 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1724 uu____1725 in
               fail uu____1723
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1738 = revert_all_hd xs1 in
        bind uu____1738 (fun uu____1740  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1744 =
      let uu____1745 = FStar_Syntax_Subst.compress x in
      uu____1745.FStar_Syntax_Syntax.n in
    match uu____1744 with
    | FStar_Syntax_Syntax.Tm_name uu____1748 -> true
    | uu____1749 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1753 =
      let uu____1754 = FStar_Syntax_Subst.compress x in
      uu____1754.FStar_Syntax_Syntax.n in
    match uu____1753 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1758 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun t  ->
    let uu____1770 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1770 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____1782)::(rhs,uu____1784)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____1810 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____1810 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____1882 =
               let uu____1890 = as_name x in (uu____1890, e, rhs) in
             Some uu____1882
         | uu____1902 -> None)
    | uu____1911 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____1934 -> fail "expected at most one goal remaining"))
let goal_to_string: goal -> Prims.string =
  fun g1  ->
    let g1_binders =
      let uu____1940 = FStar_TypeChecker_Env.all_binders g1.context in
      FStar_All.pipe_right uu____1940
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____1941 = FStar_Syntax_Print.term_to_string g1.goal_ty in
    FStar_Util.format2 "%s |- %s" g1_binders uu____1941
let merge_sub_goals: Prims.unit tac =
  let uu____1943 =
    bind get
      (fun p  ->
         match p.goals with
         | g1::g2::rest ->
             let uu____1951 =
               ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                  (FStar_Option.isNone g1.witness))
                 && (FStar_Option.isNone g2.witness) in
             if uu____1951
             then
               let uu____1953 =
                 let uu___103_1954 = p in
                 let uu____1955 =
                   let uu____1957 = conj_goals g1 g2 in uu____1957 :: rest in
                 {
                   main_context = (uu___103_1954.main_context);
                   main_goal = (uu___103_1954.main_goal);
                   all_implicits = (uu___103_1954.all_implicits);
                   goals = uu____1955;
                   smt_goals = (uu___103_1954.smt_goals);
                   transaction = (uu___103_1954.transaction)
                 } in
               set uu____1953
             else
               (let g1_binders =
                  let uu____1960 =
                    FStar_TypeChecker_Env.all_binders g1.context in
                  FStar_All.pipe_right uu____1960
                    (FStar_Syntax_Print.binders_to_string ", ") in
                let g2_binders =
                  let uu____1962 =
                    FStar_TypeChecker_Env.all_binders g2.context in
                  FStar_All.pipe_right uu____1962
                    (FStar_Syntax_Print.binders_to_string ", ") in
                let uu____1963 =
                  let uu____1964 = goal_to_string g1 in
                  let uu____1965 = goal_to_string g2 in
                  let uu____1966 =
                    let uu____1967 =
                      FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                    FStar_All.pipe_right uu____1967 FStar_Util.string_of_bool in
                  FStar_Util.format3
                    "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                    uu____1964 uu____1965 uu____1966 in
                fail uu____1963)
         | uu____1968 ->
             let goals =
               let uu____1971 =
                 FStar_All.pipe_right p.goals
                   (FStar_List.map
                      (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
               FStar_All.pipe_right uu____1971 (FStar_String.concat "\n\t") in
             let uu____1977 =
               FStar_Util.format1
                 "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
                 goals in
             fail uu____1977) in
  name_tac "merge_sub_goals" uu____1943
let rec visit: Prims.unit tac -> Prims.unit tac =
  fun callback  ->
    let uu____1985 =
      let uu____1987 =
        with_cur_goal "visit_strengthen_else"
          (fun goal  ->
             let uu____1990 =
               FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
             match uu____1990 with
             | None  ->
                 let uu____1993 =
                   let uu____1994 = FStar_Syntax_Subst.compress goal.goal_ty in
                   uu____1994.FStar_Syntax_Syntax.n in
                 (match uu____1993 with
                  | FStar_Syntax_Syntax.Tm_meta uu____1998 ->
                      let uu____2003 = visit callback in map_meta uu____2003
                  | uu____2005 ->
                      ((let uu____2007 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        FStar_Util.print1 "Not a formula, split to smt %s\n"
                          uu____2007);
                       smt))
             | Some (FStar_Syntax_Util.QEx uu____2008) ->
                 ((let uu____2013 =
                     FStar_Syntax_Print.term_to_string goal.goal_ty in
                   FStar_Util.print1
                     "Not yet handled: exists\n\tGoal is %s\n" uu____2013);
                  ret ())
             | Some (FStar_Syntax_Util.QAll (xs,uu____2015,uu____2016)) ->
                 bind intros
                   (fun binders  ->
                      let uu____2018 = visit callback in
                      let uu____2020 =
                        let uu____2022 =
                          let uu____2024 = FStar_List.map Prims.fst binders in
                          revert_all_hd uu____2024 in
                        bind uu____2022
                          (fun uu____2028  ->
                             with_cur_goal "inner"
                               (fun goal1  ->
                                  (let uu____2031 = goal_to_string goal1 in
                                   FStar_Util.print1
                                     "After reverting intros, goal is %s\n"
                                     uu____2031);
                                  ret ())) in
                      seq uu____2018 uu____2020)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2033)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
                 let uu____2034 =
                   let uu____2036 = visit callback in seq split uu____2036 in
                 bind uu____2034 (fun uu____2038  -> merge_sub_goals)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2040)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
                 bind imp_intro
                   (fun h  ->
                      let uu____2042 = visit callback in
                      seq uu____2042 revert)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2045)) ->
                 or_else trivial smt) in
      or_else callback uu____1987 in
    focus_cur_goal "visit_strengthen" uu____1985
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> proofstate =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____2053 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2053 } in
      let uu____2054 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2054
      }