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
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____446  -> add_goals [g])
let add_implicits: FStar_TypeChecker_Env.implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_453 = p in
            {
              main_context = (uu___84_453.main_context);
              main_goal = (uu___84_453.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_453.goals);
              smt_goals = (uu___84_453.smt_goals);
              transaction = (uu___84_453.transaction)
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
           (let uu___85_506 = g1 in
            let uu____507 = FStar_Syntax_Util.mk_conj t1 t2 in
            {
              context = (uu___85_506.context);
              witness = (uu___85_506.witness);
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
                 (let uu___86_546 = ps in
                  {
                    main_context = (uu___86_546.main_context);
                    main_goal = (uu___86_546.main_goal);
                    all_implicits = (uu___86_546.all_implicits);
                    goals = (g :: tl1);
                    smt_goals = (uu___86_546.smt_goals);
                    transaction = (uu___86_546.transaction)
                  }))
         | uu____547 -> Failed ("No goals left", ps))
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
        let uu____572 = FStar_Syntax_Util.term_eq e1 t in
        if uu____572 then e2 else t
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
                     (let uu___87_622 = g in
                      {
                        context = (uu___87_622.context);
                        witness = (uu___87_622.witness);
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
  with_cur_goal
    (fun g  -> bind dismiss (fun uu____636  -> add_smt_goals [g]))
let focus_cur_goal f =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals"
       | hd1::tl1 ->
           let q =
             let uu___88_653 = p in
             {
               main_context = (uu___88_653.main_context);
               main_goal = (uu___88_653.main_goal);
               all_implicits = (uu___88_653.all_implicits);
               goals = [hd1];
               smt_goals = (uu___88_653.smt_goals);
               transaction = (uu___88_653.transaction)
             } in
           let uu____654 = set q in
           bind uu____654
             (fun uu____656  ->
                bind f
                  (fun a  ->
                     bind get
                       (fun q'  ->
                          let q2 =
                            let uu___89_660 = q' in
                            {
                              main_context = (uu___89_660.main_context);
                              main_goal = (uu___89_660.main_goal);
                              all_implicits = (uu___89_660.all_implicits);
                              goals = (FStar_List.append q'.goals tl1);
                              smt_goals = (uu___89_660.smt_goals);
                              transaction = (uu___89_660.transaction)
                            } in
                          let uu____661 = set q2 in
                          bind uu____661 (fun uu____663  -> ret a)))))
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
          let uu____684 = FStar_Syntax_Subst.compress t in
          uu____684.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____707 =
                let uu____717 = ff hd1 in
                let uu____718 =
                  FStar_List.map
                    (fun uu____726  ->
                       match uu____726 with
                       | (a,q) -> let uu____733 = ff a in (uu____733, q))
                    args in
                (uu____717, uu____718) in
              FStar_Syntax_Syntax.Tm_app uu____707
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____762 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____762 with
               | (bs1,t') ->
                   let t'' =
                     let uu____768 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____768 t' in
                   let uu____769 =
                     let uu____784 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____784, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____769)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____803 -> tn in
        f env
          (let uu___90_804 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___90_804.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos = (uu___90_804.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___90_804.FStar_Syntax_Syntax.vars)
           })
exception Pointwise_Fail of Prims.string
let uu___is_Pointwise_Fail: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Pointwise_Fail uu____814 -> true
    | uu____815 -> false
let __proj__Pointwise_Fail__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | Pointwise_Fail uu____822 -> uu____822
let pointwise_rec:
  proofstate ->
    Prims.unit tac ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun tau  ->
      fun env  ->
        fun t  ->
          let env1 =
            let uu___91_838 = env in
            {
              FStar_TypeChecker_Env.solver =
                (uu___91_838.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___91_838.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___91_838.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___91_838.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___91_838.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___91_838.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___91_838.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___91_838.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___91_838.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp = false;
              FStar_TypeChecker_Env.effects =
                (uu___91_838.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___91_838.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___91_838.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___91_838.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___91_838.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___91_838.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___91_838.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___91_838.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___91_838.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___91_838.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___91_838.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___91_838.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___91_838.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___91_838.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___91_838.FStar_TypeChecker_Env.proof_ns)
            } in
          let uu____839 = FStar_TypeChecker_TcTerm.tc_term env1 t in
          match uu____839 with
          | (t1,lcomp,g) ->
              let uu____846 =
                (let uu____847 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____847) ||
                  (let uu____848 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____848) in
              if uu____846
              then t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____853 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env1 typ in
                 match uu____853 with
                 | (ut,uvs,guard) ->
                     ((let uu____870 = FStar_ST.read tacdbg in
                       if uu____870
                       then
                         let uu____873 = FStar_Syntax_Print.term_to_string t1 in
                         let uu____874 = FStar_Syntax_Print.term_to_string ut in
                         FStar_Util.print2
                           "Pointwise_rec: making equality %s = %s\n"
                           uu____873 uu____874
                       else ());
                      (let g' =
                         let uu____877 =
                           let uu____878 =
                             FStar_TypeChecker_TcTerm.universe_of env1 typ in
                           FStar_Syntax_Util.mk_eq2 uu____878 typ t1 ut in
                         {
                           context = env1;
                           witness = None;
                           goal_ty = uu____877
                         } in
                       let ps' =
                         let uu___92_880 = ps in
                         {
                           main_context = (uu___92_880.main_context);
                           main_goal = (uu___92_880.main_goal);
                           all_implicits = (uu___92_880.all_implicits);
                           goals = [g'];
                           smt_goals = [];
                           transaction = (uu___92_880.transaction)
                         } in
                       let uu____881 = run tau ps' in
                       match uu____881 with
                       | Success ((),ps'1) ->
                           (FStar_TypeChecker_Rel.force_trivial_guard env1
                              guard;
                            (let uu____886 = FStar_ST.read tacdbg in
                             if uu____886
                             then
                               let uu____889 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print1
                                 "Pointwise_rec: Suceeded! Returning %s\n"
                                 uu____889
                             else ());
                            ut)
                       | Failed (s,ps'1) -> t1)))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    let uu____900 =
      mk_tac
        (fun ps  ->
           let g =
             match ps.goals with
             | g::[] -> g
             | gs ->
                 let uu____907 =
                   let uu____908 =
                     FStar_Util.string_of_int (FStar_List.length gs) in
                   FStar_Util.format1 "pointwise: got %s goals?" uu____908 in
                 failwith uu____907 in
           let gt1 = g.goal_ty in
           try
             (let uu____917 = FStar_ST.read tacdbg in
              if uu____917
              then
                let uu____920 = FStar_Syntax_Print.term_to_string gt1 in
                FStar_Util.print1 "Pointwise starting with %s\n" uu____920
              else ());
             (let gt' = bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
              (let uu____924 = FStar_ST.read tacdbg in
               if uu____924
               then
                 let uu____927 = FStar_Syntax_Print.term_to_string gt' in
                 FStar_Util.print1
                   "Pointwise seems to have succeded with %s\n" uu____927
               else ());
              Success
                ((),
                  ((let uu___95_929 = ps in
                    {
                      main_context = (uu___95_929.main_context);
                      main_goal = (uu___95_929.main_goal);
                      all_implicits = (uu___95_929.all_implicits);
                      goals =
                        [(let uu___96_930 = g in
                          {
                            context = (uu___96_930.context);
                            witness = (uu___96_930.witness);
                            goal_ty = gt'
                          })];
                      smt_goals = (uu___95_929.smt_goals);
                      transaction = (uu___95_929.transaction)
                    }))))
           with
           | Pointwise_Fail s ->
               Failed ((Prims.strcat "pointwise_rec failed: " s), ps)) in
    focus_cur_goal uu____900
let cur_goal_and_rest f g =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret (None, None)
       | uu____973::[] -> bind f (fun a  -> ret ((Some a), None))
       | hd1::tl1 ->
           bind dismiss_all
             (fun uu____992  ->
                let uu____993 = add_goals [hd1] in
                bind uu____993
                  (fun uu____999  ->
                     bind f
                       (fun a  ->
                          bind get
                            (fun uu____1009  ->
                               match uu____1009 with
                               | { main_context = uu____1015;
                                   main_goal = uu____1016;
                                   all_implicits = uu____1017;
                                   goals = sub_goals_f;
                                   smt_goals = uu____1019;
                                   transaction = uu____1020;_} ->
                                   bind dismiss_all
                                     (fun uu____1027  ->
                                        let uu____1028 = add_goals tl1 in
                                        bind uu____1028
                                          (fun uu____1034  ->
                                             bind g
                                               (fun b  ->
                                                  let uu____1040 =
                                                    add_goals sub_goals_f in
                                                  bind uu____1040
                                                    (fun uu____1046  ->
                                                       ret
                                                         ((Some a), (Some b)))))))))))
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____1071 = t1.tac_f p in
       match uu____1071 with | Failed uu____1074 -> t2.tac_f p | q -> q)
let rec map t =
  mk_tac
    (fun ps  ->
       let uu____1092 =
         let uu____1095 =
           let uu____1102 = map t in cur_goal_and_rest t uu____1102 in
         bind uu____1095
           (fun uu___79_1112  ->
              match uu___79_1112 with
              | (None ,None ) -> ret []
              | (None ,Some uu____1125) -> failwith "impossible"
              | (Some hd1,None ) -> ret [hd1]
              | (Some hd1,Some tl1) -> ret (hd1 :: tl1)) in
       run uu____1092 ps)
let map_goal_term:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> Prims.unit tac =
  fun f  ->
    let aux =
      with_cur_goal
        (fun g  ->
           let uu____1161 =
             let uu___97_1162 = g in
             let uu____1163 = f g.goal_ty in
             {
               context = (uu___97_1162.context);
               witness = (uu___97_1162.witness);
               goal_ty = uu____1163
             } in
           replace_cur uu____1161) in
    let uu____1164 = map aux in bind uu____1164 (fun uu____1168  -> ret ())
let map_meta t =
  with_cur_goal
    (fun g  ->
       let uu____1181 =
         let uu____1182 = FStar_Syntax_Subst.compress g.goal_ty in
         uu____1182.FStar_Syntax_Syntax.n in
       match uu____1181 with
       | FStar_Syntax_Syntax.Tm_meta (f,annot) ->
           let uu____1192 =
             replace_cur
               (let uu___98_1194 = g in
                {
                  context = (uu___98_1194.context);
                  witness = (uu___98_1194.witness);
                  goal_ty = f
                }) in
           bind uu____1192
             (fun uu____1195  ->
                bind t
                  (fun a  ->
                     let uu____1197 =
                       map_goal_term
                         (fun tm  ->
                            let uu____1200 = is_true tm in
                            if uu____1200
                            then tm
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (tm, annot))
                                None tm.FStar_Syntax_Syntax.pos) in
                     bind uu____1197 (fun uu____1206  -> ret a)))
       | uu____1207 -> fail "Not a meta")
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1220 =
        bind t1
          (fun uu____1222  ->
             let uu____1223 = map t2 in
             bind uu____1223 (fun uu____1227  -> ret ())) in
      focus_cur_goal uu____1220
let intros: FStar_Syntax_Syntax.binders tac =
  with_cur_goal
    (fun goal  ->
       let uu____1231 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1231 with
       | Some (FStar_Syntax_Util.QAll (bs,pats,body)) ->
           let new_context =
             FStar_TypeChecker_Env.push_binders goal.context bs in
           let new_goal =
             { context = new_context; witness = None; goal_ty = body } in
           bind dismiss
             (fun uu____1239  ->
                let uu____1240 = add_goals [new_goal] in
                bind uu____1240
                  (fun uu____1242  ->
                     let uu____1243 =
                       FStar_All.pipe_left mlog
                         (fun uu____1248  ->
                            let uu____1249 =
                              FStar_Syntax_Print.binders_to_string ", " bs in
                            FStar_Util.print1 "intros: %s\n" uu____1249) in
                     bind uu____1243 (fun uu____1250  -> ret bs)))
       | uu____1251 -> fail "Cannot intro this goal, expected a forall")
let intros_no_names: Prims.unit tac = bind intros (fun uu____1254  -> ret ())
let mk_squash p =
  let sq = FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid in
  let uu____1265 =
    let uu____1271 = FStar_Syntax_Syntax.as_arg p in [uu____1271] in
  FStar_Syntax_Util.mk_app sq uu____1265
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option
  =
  fun t  ->
    let uu____1278 = FStar_Syntax_Util.head_and_args t in
    match uu____1278 with
    | (head1,args) ->
        let uu____1307 =
          let uu____1315 =
            let uu____1316 = FStar_Syntax_Util.un_uinst head1 in
            uu____1316.FStar_Syntax_Syntax.n in
          (uu____1315, args) in
        (match uu____1307 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____1329)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1349;
               FStar_Syntax_Syntax.index = uu____1350;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1352;
                   FStar_Syntax_Syntax.pos = uu____1353;
                   FStar_Syntax_Syntax.vars = uu____1354;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____1373 -> None)
let imp_intro: FStar_Syntax_Syntax.binder tac =
  with_cur_goal
    (fun goal  ->
       let uu____1385 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1385 with
       | Some (FStar_Syntax_Util.BaseConn
           (l,(lhs,uu____1390)::(rhs,uu____1392)::[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
           let name = FStar_Syntax_Syntax.new_bv None lhs in
           let new_goal =
             let uu____1420 = FStar_TypeChecker_Env.push_bv goal.context name in
             { context = uu____1420; witness = None; goal_ty = rhs } in
           bind dismiss
             (fun uu____1421  ->
                let uu____1422 = add_goals [new_goal] in
                bind uu____1422
                  (fun uu____1424  ->
                     let uu____1425 =
                       FStar_All.pipe_left mlog
                         (fun uu____1430  ->
                            let uu____1431 =
                              FStar_Syntax_Print.bv_to_string name in
                            FStar_Util.print1 "imp_intro: %s\n" uu____1431) in
                     bind uu____1425
                       (fun uu____1432  ->
                          let uu____1433 = FStar_Syntax_Syntax.mk_binder name in
                          ret uu____1433)))
       | uu____1434 -> fail "Cannot intro this goal, expected an '==>'")
let split: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1438 =
         FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty in
       match uu____1438 with
       | Some (FStar_Syntax_Util.BaseConn (l,args)) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid ->
           let new_goals =
             FStar_All.pipe_right args
               (FStar_List.map
                  (fun uu____1448  ->
                     match uu____1448 with
                     | (a,uu____1452) ->
                         let uu___99_1453 = goal in
                         {
                           context = (uu___99_1453.context);
                           witness = None;
                           goal_ty = a
                         })) in
           bind dismiss (fun uu____1454  -> add_goals new_goals)
       | uu____1455 -> fail "Cannot split this goal; expected a conjunction")
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
         (let uu___100_1462 = goal in
          {
            context = (uu___100_1462.context);
            witness = (uu___100_1462.witness);
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
       let uu____1468 = FStar_Syntax_Util.destruct_typ_as_formula t in
       match uu____1468 with
       | Some (FStar_Syntax_Util.BaseConn (l,[])) when
           FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid ->
           bind dismiss
             (fun uu____1481  ->
                add_goals
                  [(let uu___101_1482 = goal in
                    {
                      context = (uu___101_1482.context);
                      witness = (uu___101_1482.witness);
                      goal_ty = t
                    })])
       | uu____1483 ->
           let uu____1485 =
             let uu____1486 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format1 "Not a trivial goal: %s" uu____1486 in
           fail uu____1485)
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1496 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1496 with
           | (tm1,t,guard) ->
               let uu____1504 =
                 let uu____1505 = FStar_Syntax_Util.is_lemma t in
                 Prims.op_Negation uu____1505 in
               if uu____1504
               then fail "apply_lemma: not a lemma"
               else
                 (let uu____1508 = FStar_Syntax_Util.arrow_formals_comp t in
                  match uu____1508 with
                  | (bs,comp) ->
                      let uu____1523 =
                        FStar_List.fold_left
                          (fun uu____1540  ->
                             fun uu____1541  ->
                               match (uu____1540, uu____1541) with
                               | ((uvs,guard1,subst1),(b,aq)) ->
                                   let b_t =
                                     FStar_Syntax_Subst.subst subst1
                                       b.FStar_Syntax_Syntax.sort in
                                   let uu____1590 =
                                     FStar_TypeChecker_Util.new_implicit_var
                                       "apply_lemma"
                                       (goal.goal_ty).FStar_Syntax_Syntax.pos
                                       goal.context b_t in
                                   (match uu____1590 with
                                    | (u,uu____1605,g_u) ->
                                        let uu____1613 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 g_u in
                                        (((u, aq) :: uvs), uu____1613,
                                          ((FStar_Syntax_Syntax.NT (b, u)) ::
                                          subst1)))) ([], guard, []) bs in
                      (match uu____1523 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp in
                           let uu____1645 =
                             let c = FStar_Syntax_Util.comp_to_comp_typ comp1 in
                             match c.FStar_Syntax_Syntax.effect_args with
                             | pre::post::uu____1661 ->
                                 ((Prims.fst pre), (Prims.fst post))
                             | uu____1691 ->
                                 failwith "Impossible: not a lemma" in
                           (match uu____1645 with
                            | (pre,post) ->
                                let uu____1714 =
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context post goal.goal_ty in
                                (match uu____1714 with
                                 | None  ->
                                     let uu____1717 =
                                       let uu____1718 =
                                         FStar_Syntax_Print.term_to_string
                                           post in
                                       let uu____1719 =
                                         FStar_Syntax_Print.term_to_string
                                           goal.goal_ty in
                                       FStar_Util.format2
                                         "apply_lemma: does not unify with goal: %s vs %s"
                                         uu____1718 uu____1719 in
                                     fail uu____1717
                                 | Some g ->
                                     let g1 =
                                       let uu____1722 =
                                         FStar_TypeChecker_Rel.solve_deferred_constraints
                                           goal.context g in
                                       FStar_All.pipe_right uu____1722
                                         FStar_TypeChecker_Rel.resolve_implicits in
                                     let solution =
                                       (FStar_Syntax_Syntax.mk_Tm_app tm1
                                          uvs1) None
                                         (goal.context).FStar_TypeChecker_Env.range in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1758  ->
                                               match uu____1758 with
                                               | (uu____1765,uu____1766,uu____1767,tm2,uu____1769,uu____1770)
                                                   ->
                                                   let uu____1771 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2 in
                                                   (match uu____1771 with
                                                    | (hd1,uu____1782) ->
                                                        let uu____1797 =
                                                          let uu____1798 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1 in
                                                          uu____1798.FStar_Syntax_Syntax.n in
                                                        (match uu____1797
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1801 ->
                                                             true
                                                         | uu____1810 ->
                                                             false)))) in
                                     (solve goal solution;
                                      (let sub_goals =
                                         let uu____1814 =
                                           FStar_All.pipe_right implicits1
                                             (FStar_List.map
                                                (fun uu____1830  ->
                                                   match uu____1830 with
                                                   | (_msg,_env,_uvar,term,typ,uu____1842)
                                                       ->
                                                       {
                                                         context =
                                                           (goal.context);
                                                         witness =
                                                           (Some term);
                                                         goal_ty = typ
                                                       })) in
                                         (let uu___104_1843 = goal in
                                          {
                                            context = (uu___104_1843.context);
                                            witness = None;
                                            goal_ty = pre
                                          }) :: uu____1814 in
                                       let uu____1844 =
                                         add_implicits
                                           g1.FStar_TypeChecker_Env.implicits in
                                       bind uu____1844
                                         (fun uu____1846  ->
                                            bind dismiss
                                              (fun uu____1847  ->
                                                 add_goals sub_goals))))))))
         with | uu____1850 -> fail "apply_lemma: ill-typed term")
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    with_cur_goal
      (fun goal  ->
         try
           let uu____1860 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
           match uu____1860 with
           | (uu____1865,t,guard) ->
               let uu____1868 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty in
               if uu____1868
               then
                 (solve goal tm;
                  replace_cur
                    (let uu___107_1871 = goal in
                     {
                       context = (uu___107_1871.context);
                       witness = None;
                       goal_ty = FStar_Syntax_Util.t_true
                     }))
               else
                 (let msg =
                    let uu____1874 = FStar_Syntax_Print.term_to_string tm in
                    let uu____1875 = FStar_Syntax_Print.term_to_string t in
                    let uu____1876 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____1874
                      uu____1875 uu____1876 in
                  fail msg)
         with
         | e ->
             let uu____1880 =
               let uu____1881 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format1 "Term is not typeable: %s" uu____1881 in
             fail uu____1880)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    with_cur_goal
      (fun goal  ->
         let uu____1888 =
           FStar_All.pipe_left mlog
             (fun uu____1893  ->
                let uu____1894 =
                  FStar_Syntax_Print.bv_to_string (Prims.fst h) in
                let uu____1895 =
                  FStar_Syntax_Print.term_to_string
                    (Prims.fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1894
                  uu____1895) in
         bind uu____1888
           (fun uu____1896  ->
              let uu____1897 =
                let uu____1899 =
                  let uu____1900 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (Prims.fst h) in
                  FStar_All.pipe_left Prims.fst uu____1900 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1899 in
              match uu____1897 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1907::(x,uu____1909)::(e,uu____1911)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____1945 =
                    let uu____1946 = FStar_Syntax_Subst.compress x in
                    uu____1946.FStar_Syntax_Syntax.n in
                  (match uu____1945 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___108_1952 = goal in
                         let uu____1953 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___108_1952.context);
                           witness = (uu___108_1952.witness);
                           goal_ty = uu____1953
                         } in
                       replace_cur goal1
                   | uu____1956 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____1957 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____1961 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____1961 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns = FStar_Syntax_Free.names goal.goal_ty in
           let uu____1974 = FStar_Util.set_mem x fns in
           if uu____1974
           then fail "Cannot clear; variable appears in goal"
           else
             (let new_goal =
                let uu___109_1978 = goal in
                {
                  context = env';
                  witness = (uu___109_1978.witness);
                  goal_ty = (uu___109_1978.goal_ty)
                } in
              bind dismiss (fun uu____1979  -> add_goals [new_goal])))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____1986 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____1986 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  with_cur_goal
    (fun goal  ->
       let uu____2001 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2001 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let fvs = FStar_Syntax_Free.names goal.goal_ty in
           let new_goal =
             let uu____2015 = FStar_Util.set_mem x fvs in
             if uu____2015
             then
               let uu___110_2016 = goal in
               let uu____2017 =
                 let uu____2018 =
                   FStar_TypeChecker_TcTerm.universe_of env'
                     x.FStar_Syntax_Syntax.sort in
                 FStar_Syntax_Util.mk_forall uu____2018 x goal.goal_ty in
               {
                 context = env';
                 witness = (uu___110_2016.witness);
                 goal_ty = uu____2017
               }
             else
               (let uu___111_2020 = goal in
                let uu____2021 =
                  FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort
                    goal.goal_ty in
                {
                  context = env';
                  witness = (uu___111_2020.witness);
                  goal_ty = uu____2021
                }) in
           bind dismiss (fun uu____2022  -> add_goals [new_goal]))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    with_cur_goal
      (fun goal  ->
         let uu____2029 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2029 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2041 =
                 let uu____2042 = FStar_Syntax_Print.bv_to_string x in
                 let uu____2043 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____2042 uu____2043 in
               fail uu____2041
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2056 = revert_all_hd xs1 in
        bind uu____2056 (fun uu____2058  -> revert_hd x)
let is_name: FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    let uu____2062 =
      let uu____2063 = FStar_Syntax_Subst.compress x in
      uu____2063.FStar_Syntax_Syntax.n in
    match uu____2062 with
    | FStar_Syntax_Syntax.Tm_name uu____2066 -> true
    | uu____2067 -> false
let as_name: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu____2071 =
      let uu____2072 = FStar_Syntax_Subst.compress x in
      uu____2072.FStar_Syntax_Syntax.n in
    match uu____2071 with
    | FStar_Syntax_Syntax.Tm_name x1 -> x1
    | uu____2076 -> failwith "Not a name"
let destruct_equality_imp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun t  ->
    let uu____2088 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____2088 with
    | Some (FStar_Syntax_Util.BaseConn
        (l,(lhs,uu____2100)::(rhs,uu____2102)::[])) when
        FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid ->
        let uu____2128 = FStar_Syntax_Util.destruct_typ_as_formula lhs in
        (match uu____2128 with
         | Some (FStar_Syntax_Util.BaseConn (eq1,_::(x,_)::(e,_)::[]))|Some
           (FStar_Syntax_Util.BaseConn (eq1,(x,_)::(e,_)::[])) when
             (FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) &&
               (is_name x)
             ->
             let uu____2200 =
               let uu____2208 = as_name x in (uu____2208, e, rhs) in
             Some uu____2200
         | uu____2220 -> None)
    | uu____2229 -> None
let at_most_one t =
  bind t
    (fun a  ->
       bind get
         (fun p  ->
            match p.goals with
            | []|_::[] -> ret a
            | uu____2252 -> fail "expected at most one goal remaining"))
let merge_sub_goals: Prims.unit tac =
  bind get
    (fun p  ->
       match p.goals with
       | g1::g2::rest ->
           let uu____2261 =
             ((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) &&
                (FStar_Option.isNone g1.witness))
               && (FStar_Option.isNone g2.witness) in
           if uu____2261
           then
             let uu____2263 =
               let uu___112_2264 = p in
               let uu____2265 =
                 let uu____2267 = conj_goals g1 g2 in uu____2267 :: rest in
               {
                 main_context = (uu___112_2264.main_context);
                 main_goal = (uu___112_2264.main_goal);
                 all_implicits = (uu___112_2264.all_implicits);
                 goals = uu____2265;
                 smt_goals = (uu___112_2264.smt_goals);
                 transaction = (uu___112_2264.transaction)
               } in
             set uu____2263
           else
             (let g1_binders =
                let uu____2270 = FStar_TypeChecker_Env.all_binders g1.context in
                FStar_All.pipe_right uu____2270
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let g2_binders =
                let uu____2272 = FStar_TypeChecker_Env.all_binders g2.context in
                FStar_All.pipe_right uu____2272
                  (FStar_Syntax_Print.binders_to_string ", ") in
              let uu____2273 =
                let uu____2274 = goal_to_string g1 in
                let uu____2275 = goal_to_string g2 in
                let uu____2276 =
                  let uu____2277 =
                    FStar_TypeChecker_Env.eq_gamma g1.context g2.context in
                  FStar_All.pipe_right uu____2277 FStar_Util.string_of_bool in
                FStar_Util.format3
                  "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                  uu____2274 uu____2275 uu____2276 in
              fail uu____2273)
       | uu____2278 ->
           let goals =
             let uu____2281 =
               FStar_All.pipe_right p.goals
                 (FStar_List.map
                    (fun x  -> FStar_Syntax_Print.term_to_string x.goal_ty)) in
             FStar_All.pipe_right uu____2281 (FStar_String.concat "\n\t") in
           let uu____2287 =
             FStar_Util.format1
               "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s"
               goals in
           fail uu____2287)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___113_2297 = g in
           {
             context = ctx';
             witness = (uu___113_2297.witness);
             goal_ty = (uu___113_2297.goal_ty)
           } in
         bind dismiss (fun uu____2298  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    with_cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___114_2308 = g in
           {
             context = ctx';
             witness = (uu___114_2308.witness);
             goal_ty = (uu___114_2308.goal_ty)
           } in
         bind dismiss (fun uu____2309  -> add_goals [g']))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2313 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2317 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2321 -> false
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
        let uu____2338 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env g in
        { context = env; witness = None; goal_ty = uu____2338 } in
      let uu____2339 = FStar_Unionfind.new_transaction () in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = [];
        transaction = uu____2339
      }