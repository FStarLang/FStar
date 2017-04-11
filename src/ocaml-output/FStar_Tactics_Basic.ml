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
type 'a tac =
  {
  tac_f: proofstate -> 'a result;
  tac_name: Prims.string;
  kernel: Prims.bool;}
let as_tac name b f = { tac_f = f; tac_name = name; kernel = b }
let kernel_tac n1 t = { tac_f = t; tac_name = n1; kernel = true }
let user_tac n1 t = { tac_f = t; tac_name = n1; kernel = false }
let name_tac n1 t =
  let uu___73_300 = t in
  { tac_f = (uu___73_300.tac_f); tac_name = n1; kernel = false }
let run t p = t.tac_f p
let debug: proofstate -> Prims.string -> Prims.unit =
  fun p  ->
    fun msg  ->
      let uu____323 = FStar_Util.string_of_int (FStar_List.length p.goals) in
      let uu____327 =
        match p.goals with
        | [] -> "[]"
        | uu____328 ->
            let uu____330 =
              let uu____331 = FStar_List.hd p.goals in uu____331.goal_ty in
            FStar_Syntax_Print.term_to_string uu____330 in
      let uu____332 =
        match p.goals with
        | [] -> ""
        | uu____333 ->
            let uu____335 =
              let uu____337 = FStar_List.tl p.goals in
              FStar_All.pipe_right uu____337
                (FStar_List.map
                   (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
            FStar_All.pipe_right uu____335 (FStar_String.concat ";;") in
      FStar_Util.print4
        "TAC (ngoals=%s, maingoal=%s, rest=%s):\n\tTAC>> %s\n" uu____323
        uu____327 uu____332 msg
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  ->
    kernel_tac "print_proof_state"
      (fun p  -> let uu____349 = debug p msg; ((), p) in Success uu____349)
let ret a = kernel_tac "return" (fun p  -> Success (a, p))
let bind t1 t2 =
  kernel_tac "bind"
    (fun p  ->
       if Prims.op_Negation t1.kernel then debug p t1.tac_name else ();
       (let uu____389 = t1.tac_f p in
        match uu____389 with
        | Success (a,q) ->
            let t21 = t2 a in
            (if Prims.op_Negation t21.kernel
             then debug q t21.tac_name
             else ();
             t21.tac_f q)
        | Failed (msg,q) ->
            (if Prims.op_Negation t1.kernel
             then
               (let uu____401 = FStar_Util.format1 "%s failed!" t1.tac_name in
                debug p uu____401)
             else ();
             Failed (msg, q))))
let get: proofstate tac = kernel_tac "get" (fun p  -> Success (p, p))
let fail msg =
  kernel_tac "fail"
    (fun p  -> FStar_Util.print1 ">>>>>%s\n" msg; Failed (msg, p))
let show: Prims.unit tac =
  kernel_tac "show" (fun p  -> debug p "debug"; Success ((), p))
let set: proofstate -> Prims.unit tac =
  fun p  -> kernel_tac "set" (fun uu____423  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      match goal.witness with
      | None  -> ()
      | Some w ->
          let uu____431 =
            FStar_TypeChecker_Rel.teq_nosmt goal.context w solution in
          if uu____431
          then ()
          else
            (let uu____433 =
               let uu____434 =
                 let uu____435 = FStar_Syntax_Print.term_to_string solution in
                 let uu____436 = FStar_Syntax_Print.term_to_string w in
                 let uu____437 =
                   FStar_Syntax_Print.term_to_string goal.goal_ty in
                 FStar_Util.format3 "%s does not solve %s : %s" uu____435
                   uu____436 uu____437 in
               Failure uu____434 in
             Prims.raise uu____433)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____440 =
         let uu___74_441 = p in
         let uu____442 = FStar_List.tl p.goals in
         {
           main_context = (uu___74_441.main_context);
           main_goal = (uu___74_441.main_goal);
           all_implicits = (uu___74_441.all_implicits);
           goals = uu____442;
           smt_goals = (uu___74_441.smt_goals);
           transaction = (uu___74_441.transaction)
         } in
       set uu____440)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___75_446 = p in
          {
            main_context = (uu___75_446.main_context);
            main_goal = (uu___75_446.main_goal);
            all_implicits = (uu___75_446.all_implicits);
            goals = [];
            smt_goals = (uu___75_446.smt_goals);
            transaction = (uu___75_446.transaction)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___76_455 = p in
            {
              main_context = (uu___76_455.main_context);
              main_goal = (uu___76_455.main_goal);
              all_implicits = (uu___76_455.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___76_455.smt_goals);
              transaction = (uu___76_455.transaction)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___77_464 = p in
            {
              main_context = (uu___77_464.main_context);
              main_goal = (uu___77_464.main_goal);
              all_implicits = (uu___77_464.all_implicits);
              goals = (uu___77_464.goals);
              smt_goals = (FStar_List.append gs p.smt_goals);
              transaction = (uu___77_464.transaction)
            }))
let replace: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____470  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___78_477 = p in
            {
              main_context = (uu___78_477.main_context);
              main_goal = (uu___78_477.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___78_477.goals);
              smt_goals = (uu___78_477.smt_goals);
              transaction = (uu___78_477.transaction)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____487 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____487 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid
    | uu____499 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____504 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____504 with
    | Some (FStar_Syntax_Util.BaseConn (l,[])) ->
        FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid
    | uu____516 -> false
let conj_goals: goal -> goal -> goal =
  fun g1  ->
    fun g2  ->
      let t1 = g1.goal_ty in
      let t2 = g2.goal_ty in
      let uu____526 = (is_true t1) || (is_false t2) in
      if uu____526
      then g2
      else
        (let uu____528 = (is_true t2) || (is_false t1) in
         if uu____528
         then g1
         else
           (let uu___79_530 = g1 in
            let uu____531 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___79_530.context);
              witness = (uu___79_530.witness);
              goal_ty = uu____531
            }))
let with_cur_goal nm f =
  let uu____552 =
    bind get
      (fun p  ->
         match p.goals with | [] -> fail "No more goals" | hd1::tl1 -> f hd1) in
  name_tac nm uu____552
let smt: Prims.unit tac =
  with_cur_goal "smt"
    (fun g  ->
       bind dismiss
         (fun uu____561  ->
            let uu____562 =
              add_goals
                [(let uu___80_564 = g in
                  {
                    context = (uu___80_564.context);
                    witness = (uu___80_564.witness);
                    goal_ty = FStar_Syntax_Util.t_true
                  })] in
            bind uu____562 (fun uu____565  -> add_smt_goals [g])))
let focus_cur_goal nm f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___81_587 = p in
             {
               main_context = (uu___81_587.main_context);
               main_goal = (uu___81_587.main_goal);
               all_implicits = (uu___81_587.all_implicits);
               goals = [hd1];
               smt_goals = (uu___81_587.smt_goals);
               transaction = (uu___81_587.transaction)
             } in
           let uu____588 = set q in
           bind uu____588
             (fun uu____590  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___82_594 = q' in
                            {
                              main_context = (uu___82_594.main_context);
                              main_goal = (uu___82_594.main_goal);
                              all_implicits = (uu___82_594.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___82_594.smt_goals);
                              transaction = (uu___82_594.transaction)
                            } in
                          let uu____595 = set q2 in
                          bind uu____595 (fun uu____597  -> ret a)))))
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | uu____631::[] -> bind f (fun a  -> ret (a, None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____646  ->
                let uu____647 = add_goals [hd1] in
                bind uu____647
                  (fun uu____652  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____660  ->
                               match uu____660 with
                               | { main_context = uu____665;
                                   main_goal = uu____666;
                                   all_implicits = uu____667;
                                   goals = sub_goals_f;
                                   smt_goals = uu____669;
                                   transaction = uu____670;_} ->
                                   bind dismiss_all
                                     (fun uu____676  ->
                                        let uu____677 = add_goals tl1 in
                                        bind uu____677
                                          (fun uu____682  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____687 =
                                                    add_goals sub_goals_f in
                                                  bind uu____687
                                                    (fun uu____692  ->
                                                       ret (a, (Some b)))))))))))
let or_else t1 t2 =
  kernel_tac "or_else"
    (fun p  ->
       (let uu____716 = FStar_Util.format1 "or_else: trying %s" t1.tac_name in
        debug p uu____716);
       (let uu____717 = t1.tac_f p in
        match uu____717 with
        | Failed uu____720 ->
            ((let uu____724 =
                FStar_Util.format2 "or_else: %s failed; trying %s"
                  t1.tac_name t2.tac_name in
              debug p uu____724);
             t2.tac_f p)
        | q -> q))
let rec map t =
  user_tac "map"
    (fun p  ->
       let uu____740 =
         let uu____743 =
           let uu____749 = map t in cur_goal_and_rest t uu____749 in
         bind uu____743
           (fun uu___72_758  ->
              match uu___72_758 with
              | (hd1,None ) -> ret [hd1]
              | (hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____740 p)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal "map_goal"
        (fun g  ->
           let uu____791 =
             let uu___83_792 = g in
             let uu____793 = f g.goal_ty in
             {
               context = (uu___83_792.context);
               witness = (uu___83_792.witness);
               goal_ty = uu____793
             } in
           replace uu____791) in
    let uu____794 = map aux in bind uu____794 (fun uu____798  -> ret ())
let map_meta t =
  with_cur_goal "map_meta"
    (fun g  ->
       let uu____811 =
         let uu____812 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____812.FStar_Syntax_Syntax.n in
       match uu____811 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____822 =
             replace
               (let uu___84_824 = g in
                {
                  context = (uu___84_824.context);
                  witness = (uu___84_824.witness);
                  goal_ty = f
                }) in
           bind uu____822
             (fun uu____825  ->
                bind t
                  (fun a  ->
                     let uu____827 =
                       map_goal_term
                         (fun tm  ->
                            let uu____830 = is_true tm in
                            if uu____830
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____827 (fun uu____836  -> ret a)))
       | uu____837 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____850 =
        bind t1
          (fun uu____852  ->
             let uu____853 = map t2 in
             bind uu____853 (fun uu____857  -> ret ())) in
      focus_cur_goal "seq" uu____850
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal "intros"
    (fun goal  ->
       let uu____861 = FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____861 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____869  ->
                let uu____870 = add_goals [new_goal] in
                bind uu____870
                  (fun uu____872  ->
                     (let uu____874 =
                        FStar_Syntax_Print.binders_to_string ", " bs in
                      FStar_Util.print1 "intros: %s\n" uu____874);
                     ret bs))
       | uu____875 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____878  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____889 = let uu____895 = FStar_Syntax_Syntax.as_arg p in [uu____895] in
  FStar_Syntax_Util.mk_app sq uu____889
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____902 = FStar_Syntax_Util.head_and_args t in
    match uu____902 with
    | (head1,args) ->
        let uu____931 =
          let uu____939 =
            let uu____940 = FStar_Syntax_Util.un_uinst head1 in
            uu____940.FStar_Syntax_Syntax.n in
          (uu____939, args) in
        (match uu____931 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____953)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____973;
               FStar_Syntax_Syntax.index = uu____974;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____976;
                   FStar_Syntax_Syntax.pos = uu____977;
                   FStar_Syntax_Syntax.vars = uu____978;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____997 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal "imp_intro"
    (fun goal  ->
       let uu____1009 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1009 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1014)::(rhs,uu____1016)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1044 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1044; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1045  ->
                let uu____1046 = add_goals [new_goal] in
                bind uu____1046
                  (fun uu____1048  ->
                     (let uu____1050 = FStar_Syntax_Print.bv_to_string name in
                      FStar_Util.print1 "imp_intro: %s\n" uu____1050);
                     (let uu____1051 = FStar_Syntax_Syntax.mk_binder name in
                      ret uu____1051)))
       | uu____1052 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal "split"
    (fun goal  ->
       let uu____1056 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1056 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1066  ->
                     match uu____1066 with
                     | (a,uu____1070) ->
                         let uu___85_1071 = goal in
                         {
                           context = (uu___85_1071.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss
             (fun uu____1072  ->
                let uu____1073 = add_goals new_goals in
                bind uu____1073 (fun uu____1075  -> show))
       | uu____1076 -> fail "Cannot split this goal; expected a conjunction")
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
       let uu____1083 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1083 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid ->
           bind dismiss
             (fun uu____1096  ->
                add_goals
                  [(let uu___86_1097 = goal in
                    {
                      context = (uu___86_1097.context);
                      witness = (uu___86_1097.witness);
                      goal_ty = t
                    })])
       | uu____1098 -> fail "Not a trivial goal")
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "apply_lemma"
      (fun goal  ->
         try
           let uu____1109 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1109 with
           | (tm1,t,guard) ->
               let uu____1117 =
                 let uu____1118 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1118 in
               if uu____1117
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1121 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1121 with
                  | (bs,comp) ->
                      let uu____1136 =
                        FStar_List.fold_left
                          (fun uu____1153  ->
                             fun uu____1154  ->
                               match (uu____1153, uu____1154) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1203 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1203 with
                                    | (u,uu____1218,g_u) ->
                                        let uu____1226 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1226,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1136 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1258 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1274 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1304 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1258 with
                            | (pre,post) ->
                                let uu____1327 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1327 with
                                 | None  ->
                                     fail
                                       "apply_lemma: does not unify with goal"
                                 | Some g ->
                                     let g1 =
                                       let uu____1332 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1332
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1368  ->
                                               match uu____1368 with
                                               | (uu____1375,uu____1376,uu____1377,tm2,uu____1379,uu____1380)
                                                   ->
                                                   let uu____1381 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1381 with
                                                    | (hd1,uu____1392) ->
                                                        let uu____1407 =
                                                          let uu____1408 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1408.FStar_Syntax_Syntax.n in
                                                        (match uu____1407
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1411 ->
                                                             true
                                                         | uu____1420 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____1424 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____1440  ->
                                                   match uu____1440 with
                                                   | (_msg,_env,_uvar,term,typ,uu____1452)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (Some term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___89_1453 = goal in
                                          {
                                            context = (uu___89_1453.context);
                                            witness = None;
                                            goal_ty = pre
                                          }) :: uu____1424 in
                                       let uu____1454 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1454
                                         (fun uu____1456  ->
                                            bind dismiss
                                              (fun uu____1457  ->
                                                 add_goals sub_goals))))))))
         with | uu____1460 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal "exact"
      (fun goal  ->
         try
           let uu____1470 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1470 with
           | (uu____1475,t,guard) ->
               let uu____1478 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1478
               then
                 (solve goal tm;
                  replace
                    (let uu___92_1481 = goal in
                     {
                       context = (uu___92_1481.context);
                       witness = None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____1484 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1485 = FStar_Syntax_Print.term_to_string t in
                    let uu____1486 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1484
                      uu____1485 uu____1486 in
                  fail msg)
         with
         | e ->
             let uu____1490 =
               let uu____1491 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1491 in
             fail uu____1490)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal "rewrite"
      (fun goal  ->
         (let uu____1499 = FStar_Syntax_Print.bv_to_string (Prims.fst h) in
          let uu____1500 =
            FStar_Syntax_Print.term_to_string
              (Prims.fst h).FStar_Syntax_Syntax.sort in
          FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1499 uu____1500);
         (let uu____1501 =
            let uu____1503 =
              let uu____1504 =
                FStar_TypeChecker_Env.lookup_bv goal.context (Prims.fst h) in
              FStar_All.pipe_left Prims.fst uu____1504 in
            FStar_Syntax_Util.destruct_typ_as_formula uu____1503 in
          match uu____1501 with
          | Some (FStar_Syntax_Util.BaseConn
              (l,uu____1511::(x,uu____1513)::(e,uu____1515)::[])) when
              FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
              let uu____1549 =
                let uu____1550 = FStar_Syntax_Subst.compress x in
                uu____1550.FStar_Syntax_Syntax.n in
              (match uu____1549 with
               | FStar_Syntax_Syntax.Tm_name x1 ->
                   let goal1 =
                     let uu___93_1556 = goal in
                     let uu____1557 =
                       FStar_Syntax_Subst.subst
                         [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                     {
                       context = (uu___93_1556.context);
                       witness = (uu___93_1556.witness);
                       goal_ty = uu____1557
                     } in
                   replace goal1
               | uu____1560 ->
                   fail
                     "Not an equality hypothesis with a variable on the LHS")
          | uu____1561 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal "clear"
    (fun goal  ->
       let uu____1565 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1565 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1578 = FStar_Util.set_mem x fns in
           if uu____1578
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___94_1582 = goal in
                {
                  context = env';
                  witness = (uu___94_1582.witness);
                  goal_ty = (uu___94_1582.goal_ty)
                } in
              bind dismiss (fun uu____1583  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "clear_hd"
      (fun goal  ->
         let uu____1590 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1590 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal "revert"
    (fun goal  ->
       let uu____1605 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1605 with
       | None  -> fail "Cannot clear_hd; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           ((let uu____1619 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.print1 "reverting %s\n" uu____1619);
            (let uu____1620 =
               let uu____1621 = FStar_Util.set_mem x fns in
               Prims.op_Negation uu____1621 in
             if uu____1620
             then clear_hd x
             else
               (let new_goal =
                  let uu____1625 =
                    let uu____1634 = un_squash x.FStar_Syntax_Syntax.sort in
                    let uu____1638 = un_squash goal.goal_ty in
                    (uu____1634, uu____1638) in
                  match uu____1625 with
                  | (Some p,Some q) ->
                      let uu___95_1664 = goal in
                      let uu____1665 = FStar_Syntax_Util.mk_imp p q in
                      {
                        context = env';
                        witness = (uu___95_1664.witness);
                        goal_ty = uu____1665
                      }
                  | uu____1666 ->
                      let uu___96_1675 = goal in
                      let uu____1676 =
                        let uu____1677 =
                          FStar_TypeChecker_TcTerm.universe_of env'
                            x.FStar_Syntax_Syntax.sort in
                        FStar_Syntax_Util.mk_forall uu____1677 x goal.goal_ty in
                      {
                        context = env';
                        witness = (uu___96_1675.witness);
                        goal_ty = uu____1676
                      } in
                bind dismiss (fun uu____1678  -> add_goals [new_goal])))))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal "revert_hd"
      (fun goal  ->
         let uu____1685 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1685 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____1697 =
                 let uu____1698 = FStar_Syntax_Print.bv_to_string x in
                 let uu____1699 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____1698 uu____1699 in
               fail uu____1697
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____1712 = revert_all_hd xs1 in
        bind uu____1712 (fun uu____1714  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____1718 =
      let uu____1719 = FStar_Syntax_Subst.compress x in
      uu____1719.FStar_Syntax_Syntax.n in
    match uu____1718 with
    | FStar_Syntax_Syntax.Tm_name uu____1722 -> true
    | uu____1723 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____1727 =
      let uu____1728 = FStar_Syntax_Subst.compress x in
      uu____1728.FStar_Syntax_Syntax.n in
    match uu____1727 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____1732 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun t  ->
    let uu____1744 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1744 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____1756)::(rhs,uu____1758)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____1784 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____1784 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____1856 =
               let uu____1864 = as_name x in (uu____1864, e, rhs) in
             Some uu____1856
         | uu____1876 -> None)
    | uu____1885 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____1908 -> fail "expected at most one goal remaining"))
let goal_to_string: goal -> Prims.string =
  fun g1  ->
    let g1_binders =
      let uu____1914 = FStar_TypeChecker_Env.all_binders g1.context in
      FStar_All.pipe_right uu____1914
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____1915 = FStar_Syntax_Print.term_to_string g1.goal_ty in
    FStar_Util.format2 "%s |- %s" g1_binders uu____1915
let merge_sub_goals: Prims.unit tac =
  let uu____1917 =
    bind get
      (fun p  ->
         match p.goals with
         | g1::g2::rest ->
             let uu____1925 =
               ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                  (FStar_Option.isNone g1.witness))
                 && (FStar_Option.isNone g2.witness) in
             if uu____1925
             then
               let uu____1927 =
                 let uu___97_1928 = p in
                 let uu____1929 =
                   let uu____1931 = conj_goals g1 g2 in uu____1931 :: rest in
                 {
                   main_context = (uu___97_1928.main_context);
                   main_goal = (uu___97_1928.main_goal);
                   all_implicits = (uu___97_1928.all_implicits);
                   goals = uu____1929;
                   smt_goals = (uu___97_1928.smt_goals);
                   transaction = (uu___97_1928.transaction)
                 } in
               set uu____1927
             else
               (let g1_binders =
                  let uu____1934 =
                    FStar_TypeChecker_Env.all_binders g1.context in
                  FStar_All.pipe_right uu____1934
                    (FStar_Syntax_Print.binders_to_string ", ") in
                let g2_binders =
                  let uu____1936 =
                    FStar_TypeChecker_Env.all_binders g2.context in
                  FStar_All.pipe_right uu____1936
                    (FStar_Syntax_Print.binders_to_string ", ") in
                let uu____1937 =
                  let uu____1938 = goal_to_string g1 in
                  let uu____1939 = goal_to_string g2 in
                  let uu____1940 =
                    let uu____1941 =
                      FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                    FStar_All.pipe_right uu____1941 FStar_Util.string_of_bool in
                  FStar_Util.format3
                    "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                    uu____1938 uu____1939 uu____1940 in
                fail uu____1937)
         | uu____1942 ->
             let goals =
               let uu____1945 =
                 FStar_All.pipe_right p.goals
                   (FStar_List.map
                      (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
               FStar_All.pipe_right uu____1945 (FStar_String.concat "\n\t") in
             let uu____1951 =
               FStar_Util.format1
                 "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
                 goals in
             fail uu____1951) in
  name_tac "merge_sub_goals" uu____1917
let rec visit: Prims.unit tac -> Prims.unit tac =
  fun callback  ->
    let uu____1959 =
      let uu____1961 =
        with_cur_goal "visit_strengthen_else"
          (fun goal  ->
             let uu____1964 =
               FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
             match uu____1964 with
             | None  ->
                 let uu____1967 =
                   let uu____1968 = FStar_Syntax_Subst.compress goal.goal_ty in
                   uu____1968.FStar_Syntax_Syntax.n in
                 (match uu____1967 with
                  | FStar_Syntax_Syntax.Tm_meta uu____1972 ->
                      let uu____1977 = visit callback in map_meta uu____1977
                  | uu____1979 ->
                      ((let uu____1981 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty in
                        FStar_Util.print1 "Not a formula, split to smt %s\n"
                          uu____1981);
                       smt))
             | Some (FStar_Syntax_Util.QEx uu____1982) ->
                 ((let uu____1987 =
                     FStar_Syntax_Print.term_to_string goal.goal_ty in
                   FStar_Util.print1
                     "Not yet handled: exists\n\tGoal is %s\n" uu____1987);
                  ret ())
             | Some (FStar_Syntax_Util.QAll (xs,uu____1989,uu____1990)) ->
                 bind intros
                   (fun binders  ->
                      let uu____1992 = visit callback in
                      bind uu____1992
                        (fun uu____1994  ->
                           let uu____1995 =
                             let uu____1997 =
                               FStar_List.map Prims.fst binders in
                             revert_all_hd uu____1997 in
                           bind uu____1995
                             (fun uu____2001  ->
                                with_cur_goal "inner"
                                  (fun goal1  ->
                                     (let uu____2004 = goal_to_string goal1 in
                                      FStar_Util.print1
                                        "After reverting intros, goal is %s\n"
                                        uu____2004);
                                     ret ()))))
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2006)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
                 let uu____2007 =
                   let uu____2009 = visit callback in seq split uu____2009 in
                 bind uu____2007 (fun uu____2011  -> merge_sub_goals)
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2013)) when
                 FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
                 bind imp_intro
                   (fun h  ->
                      let uu____2015 = visit callback in
                      bind uu____2015 (fun uu____2017  -> revert))
             | Some (FStar_Syntax_Util.BaseConn (l,uu____2019)) ->
                 or_else trivial smt) in
      or_else callback uu____1961 in
    focus_cur_goal "visit_strengthen" uu____1959
let proofstate_of_goal_ty:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> proofstate =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____2027 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2027 } in
      let uu____2028 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2028
      }