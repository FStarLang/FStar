open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let bnorm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun e  -> fun t  -> FStar_TypeChecker_Normalize.normalize [] e t 
type goal =
  {
  context: env ;
  witness: FStar_Syntax_Syntax.term ;
  goal_ty: FStar_Syntax_Syntax.typ ;
  opts: FStar_Options.optionstate }
type proofstate =
  {
  main_context: env ;
  main_goal: goal ;
  all_implicits: implicits ;
  goals: goal Prims.list ;
  smt_goals: goal Prims.list }
type 'a result =
  | Success of ('a * proofstate) 
  | Failed of (Prims.string * proofstate) 
let uu___is_Success projectee =
  match projectee with | Success _0 -> true | uu____114 -> false 
let __proj__Success__item___0 projectee =
  match projectee with | Success _0 -> _0 
let uu___is_Failed projectee =
  match projectee with | Failed _0 -> true | uu____145 -> false 
let __proj__Failed__item___0 projectee =
  match projectee with | Failed _0 -> _0 
exception TacFailure of Prims.string 
let uu___is_TacFailure : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | TacFailure uu____170 -> true | uu____171 -> false
  
let __proj__TacFailure__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | TacFailure uu____178 -> uu____178 
type 'a tac = {
  tac_f: proofstate -> 'a result }
let mk_tac f = { tac_f = f } 
let run t p = t.tac_f p 
let ret x = mk_tac (fun p  -> Success (x, p)) 
let bind t1 t2 =
  mk_tac
    (fun p  ->
       let uu____273 = run t1 p  in
       match uu____273 with
       | Success (a,q) -> let uu____278 = t2 a  in run uu____278 q
       | Failed (msg,q) -> Failed (msg, q))
  
let idtac : Prims.unit tac = ret () 
let goal_to_string : goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____287 = FStar_TypeChecker_Env.all_binders g.context  in
      FStar_All.pipe_right uu____287
        (FStar_Syntax_Print.binders_to_string ", ")
       in
    let uu____288 = FStar_Syntax_Print.term_to_string g.witness  in
    let uu____289 = FStar_Syntax_Print.term_to_string g.goal_ty  in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____288 uu____289
  
let tacprint : Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let tacprint1 : Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____299 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____299
  
let tacprint2 : Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____309 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____309
  
let tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____322 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____322
  
let comp_to_typ :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____327) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____335) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let is_irrelevant : goal -> Prims.bool =
  fun g  ->
    let uu____346 =
      let uu____350 =
        FStar_TypeChecker_Normalize.unfold_whnf g.context g.goal_ty  in
      FStar_Syntax_Util.un_squash uu____350  in
    match uu____346 with | Some t -> true | uu____356 -> false
  
let dump_goal ps goal =
  let uu____373 = goal_to_string goal  in tacprint uu____373 
let dump_cur : proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____381 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____384 = FStar_List.hd ps.goals  in dump_goal ps uu____384))
  
let dump_proofstate : proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____394 = FStar_Util.string_of_int (FStar_List.length ps.goals)
          in
       tacprint1 "ACTIVE goals (%s):" uu____394);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____400 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals)  in
       tacprint1 "SMT goals (%s):" uu____400);
      FStar_List.iter (dump_goal ps) ps.smt_goals
  
let print_proof_state1 : Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_cur p msg; Success ((), p)) 
let print_proof_state : Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p)) 
let get : proofstate tac = mk_tac (fun p  -> Success (p, p)) 
let tac_verb_dbg : Prims.bool option FStar_ST.ref = FStar_Util.mk_ref None 
let rec log : proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun ps  ->
    fun f  ->
      let uu____437 = FStar_ST.read tac_verb_dbg  in
      match uu____437 with
      | None  ->
          ((let uu____443 =
              let uu____445 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              Some uu____445  in
            FStar_ST.write tac_verb_dbg uu____443);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
  
let mlog : (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ()) 
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____471 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail")
           in
        if uu____471
        then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
        else ());
       Failed (msg, ps))
  
let fail1 msg x = let uu____486 = FStar_Util.format1 msg x  in fail uu____486 
let fail2 msg x y =
  let uu____505 = FStar_Util.format2 msg x y  in fail uu____505 
let fail3 msg x y z =
  let uu____529 = FStar_Util.format3 msg x y z  in fail uu____529 
let trytac t =
  mk_tac
    (fun ps  ->
       let tx = FStar_Syntax_Unionfind.new_transaction ()  in
       let uu____544 = run t ps  in
       match uu____544 with
       | Success (a,q) ->
           (FStar_Syntax_Unionfind.commit tx; Success ((Some a), q))
       | Failed (uu____553,uu____554) ->
           (FStar_Syntax_Unionfind.rollback tx; Success (None, ps)))
  
let set : proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____563  -> Success ((), p)) 
let solve : goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____570 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution
         in
      if uu____570
      then ()
      else
        (let uu____572 =
           let uu____573 =
             let uu____574 = FStar_Syntax_Print.term_to_string solution  in
             let uu____575 = FStar_Syntax_Print.term_to_string goal.witness
                in
             let uu____576 = FStar_Syntax_Print.term_to_string goal.goal_ty
                in
             FStar_Util.format3 "%s does not solve %s : %s" uu____574
               uu____575 uu____576
              in
           TacFailure uu____573  in
         raise uu____572)
  
let dismiss : Prims.unit tac =
  bind get
    (fun p  ->
       let uu____579 =
         let uu___78_580 = p  in
         let uu____581 = FStar_List.tl p.goals  in
         {
           main_context = (uu___78_580.main_context);
           main_goal = (uu___78_580.main_goal);
           all_implicits = (uu___78_580.all_implicits);
           goals = uu____581;
           smt_goals = (uu___78_580.smt_goals)
         }  in
       set uu____579)
  
let dismiss_all : Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_585 = p  in
          {
            main_context = (uu___79_585.main_context);
            main_goal = (uu___79_585.main_goal);
            all_implicits = (uu___79_585.all_implicits);
            goals = [];
            smt_goals = (uu___79_585.smt_goals)
          }))
  
let add_goals : goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_594 = p  in
            {
              main_context = (uu___80_594.main_context);
              main_goal = (uu___80_594.main_goal);
              all_implicits = (uu___80_594.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_594.smt_goals)
            }))
  
let add_smt_goals : goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_603 = p  in
            {
              main_context = (uu___81_603.main_context);
              main_goal = (uu___81_603.main_goal);
              all_implicits = (uu___81_603.all_implicits);
              goals = (uu___81_603.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
  
let push_goals : goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_612 = p  in
            {
              main_context = (uu___82_612.main_context);
              main_goal = (uu___82_612.main_goal);
              all_implicits = (uu___82_612.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___82_612.smt_goals)
            }))
  
let push_smt_goals : goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_621 = p  in
            {
              main_context = (uu___83_621.main_context);
              main_goal = (uu___83_621.main_goal);
              all_implicits = (uu___83_621.all_implicits);
              goals = (uu___83_621.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
  
let replace_cur : goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____627  -> add_goals [g]) 
let add_implicits : implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_634 = p  in
            {
              main_context = (uu___84_634.main_context);
              main_goal = (uu___84_634.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_634.goals);
              smt_goals = (uu___84_634.smt_goals)
            }))
  
let new_uvar :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) tac
  =
  fun env  ->
    fun typ  ->
      let uu____653 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____653 with
      | (u,uu____664,g_u) ->
          let uu____672 = add_implicits g_u.FStar_TypeChecker_Env.implicits
             in
          bind uu____672 (fun uu____676  -> ret (u, g_u))
  
let is_true : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____682 = FStar_Syntax_Util.un_squash t  in
    match uu____682 with
    | Some t' ->
        let uu____691 =
          let uu____692 = FStar_Syntax_Subst.compress t'  in
          uu____692.FStar_Syntax_Syntax.n  in
        (match uu____691 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____696 -> false)
    | uu____697 -> false
  
let is_false : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____704 = FStar_Syntax_Util.un_squash t  in
    match uu____704 with
    | Some t' ->
        let uu____713 =
          let uu____714 = FStar_Syntax_Subst.compress t'  in
          uu____714.FStar_Syntax_Syntax.n  in
        (match uu____713 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____718 -> false)
    | uu____719 -> false
  
let cur_goal : goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
  
let add_irrelevant_goal :
  env ->
    FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun env  ->
    fun phi  ->
      fun opts  ->
        let typ = FStar_Syntax_Util.mk_squash phi  in
        let uu____743 = new_uvar env typ  in
        bind uu____743
          (fun uu____749  ->
             match uu____749 with
             | (u,g_u) ->
                 let goal =
                   { context = env; witness = u; goal_ty = typ; opts }  in
                 add_goals [goal])
  
let smt : Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____758 = is_irrelevant g  in
       if uu____758
       then bind dismiss (fun uu____760  -> add_smt_goals [g])
       else
         (let uu____762 = FStar_Syntax_Print.term_to_string g.goal_ty  in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____762))
  
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____792 =
         try let uu____809 = FStar_List.splitAt n1 p.goals  in ret uu____809
         with | uu____824 -> fail "divide: not enough goals"  in
       bind uu____792
         (fun uu____835  ->
            match uu____835 with
            | (lgs,rgs) ->
                let lp =
                  let uu___85_850 = p  in
                  {
                    main_context = (uu___85_850.main_context);
                    main_goal = (uu___85_850.main_goal);
                    all_implicits = (uu___85_850.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  }  in
                let rp =
                  let uu___86_852 = p  in
                  {
                    main_context = (uu___86_852.main_context);
                    main_goal = (uu___86_852.main_goal);
                    all_implicits = (uu___86_852.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  }  in
                let uu____853 = set lp  in
                bind uu____853
                  (fun uu____857  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____864 = set rp  in
                               bind uu____864
                                 (fun uu____868  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___87_876 = p  in
                                                {
                                                  main_context =
                                                    (uu___87_876.main_context);
                                                  main_goal =
                                                    (uu___87_876.main_goal);
                                                  all_implicits =
                                                    (uu___87_876.all_implicits);
                                                  goals =
                                                    (FStar_List.append
                                                       lp'.goals rp'.goals);
                                                  smt_goals =
                                                    (FStar_List.append
                                                       lp'.smt_goals
                                                       (FStar_List.append
                                                          rp'.smt_goals
                                                          p.smt_goals))
                                                }  in
                                              let uu____877 = set p'  in
                                              bind uu____877
                                                (fun uu____881  -> ret (a, b))))))))))
  
let focus f =
  let uu____894 = divide (Prims.parse_int "1") f idtac  in
  bind uu____894 (fun uu____900  -> match uu____900 with | (a,()) -> ret a) 
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____921::uu____922 ->
           let uu____924 =
             let uu____929 = map tau  in
             divide (Prims.parse_int "1") tau uu____929  in
           bind uu____924
             (fun uu____937  -> match uu____937 with | (h,t) -> ret (h :: t)))
  
let seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____960 =
        bind t1
          (fun uu____962  ->
             let uu____963 = map t2  in
             bind uu____963 (fun uu____967  -> ret ()))
         in
      focus uu____960
  
let intro : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) tac =
  bind cur_goal
    (fun goal  ->
       let uu____975 = FStar_Syntax_Util.arrow_one goal.goal_ty  in
       match uu____975 with
       | Some (b,c) ->
           let uu____986 = FStar_Syntax_Subst.open_comp [b] c  in
           (match uu____986 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1006 ->
                      failwith
                        "impossible: open_comp returned different amount of binders"
                   in
                let uu____1009 =
                  let uu____1010 = FStar_Syntax_Util.is_total_comp c1  in
                  Prims.op_Negation uu____1010  in
                if uu____1009
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1]  in
                   let typ' = comp_to_typ c1  in
                   let uu____1023 = new_uvar env' typ'  in
                   bind uu____1023
                     (fun uu____1031  ->
                        match uu____1031 with
                        | (u,g) ->
                            let uu____1039 =
                              let uu____1040 =
                                FStar_Syntax_Util.abs [b1] u None  in
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                goal.witness uu____1040
                               in
                            if uu____1039
                            then
                              let uu____1048 =
                                let uu____1050 =
                                  let uu___90_1051 = goal  in
                                  let uu____1052 = bnorm env' u  in
                                  let uu____1053 = bnorm env' typ'  in
                                  {
                                    context = env';
                                    witness = uu____1052;
                                    goal_ty = uu____1053;
                                    opts = (uu___90_1051.opts)
                                  }  in
                                replace_cur uu____1050  in
                              bind uu____1048 (fun uu____1056  -> ret b1)
                            else fail "intro: unification failed")))
       | None  ->
           let uu____1064 = FStar_Syntax_Print.term_to_string goal.goal_ty
              in
           fail1 "intro: goal is not an arrow (%s)" uu____1064)
  
let norm : FStar_Reflection_Data.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let tr s1 =
           match s1 with
           | FStar_Reflection_Data.Simpl  ->
               [FStar_TypeChecker_Normalize.Simplify]
           | FStar_Reflection_Data.WHNF  ->
               [FStar_TypeChecker_Normalize.WHNF]
           | FStar_Reflection_Data.Primops  ->
               [FStar_TypeChecker_Normalize.Primops]
           | FStar_Reflection_Data.Delta  ->
               [FStar_TypeChecker_Normalize.UnfoldUntil
                  FStar_Syntax_Syntax.Delta_constant]
            in
         let steps =
           let uu____1083 =
             let uu____1085 = FStar_List.map tr s  in
             FStar_List.flatten uu____1085  in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1083
            in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness
            in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty
            in
         replace_cur
           (let uu___91_1091 = goal  in
            {
              context = (uu___91_1091.context);
              witness = w;
              goal_ty = t;
              opts = (uu___91_1091.opts)
            }))
  
let istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.Simplify;
        FStar_TypeChecker_Normalize.UnfoldTac]  in
      let t1 = FStar_TypeChecker_Normalize.normalize steps e t  in is_true t1
  
let trivial : Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____1103 = istrivial goal.context goal.goal_ty  in
       if uu____1103
       then (solve goal FStar_Syntax_Const.exp_unit; dismiss)
       else
         (let uu____1107 = FStar_Syntax_Print.term_to_string goal.goal_ty  in
          fail1 "Not a trivial goal: %s" uu____1107))
  
let exact : FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1114 =
           try
             let uu____1128 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t
                in
             ret uu____1128
           with
           | e ->
               let uu____1141 = FStar_Syntax_Print.term_to_string t  in
               let uu____1142 = FStar_Syntax_Print.tag_of_term t  in
               fail2 "exact: term is not typeable: %s (%s)" uu____1141
                 uu____1142
            in
         bind uu____1114
           (fun uu____1149  ->
              match uu____1149 with
              | (t1,typ,guard) ->
                  let uu____1157 =
                    let uu____1158 =
                      let uu____1159 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard
                         in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____1159
                       in
                    Prims.op_Negation uu____1158  in
                  if uu____1157
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____1162 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty
                        in
                     if uu____1162
                     then (solve goal t1; dismiss)
                     else
                       (let uu____1166 = FStar_Syntax_Print.term_to_string t1
                           in
                        let uu____1167 =
                          let uu____1168 = bnorm goal.context typ  in
                          FStar_Syntax_Print.term_to_string uu____1168  in
                        let uu____1169 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty  in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____1166 uu____1167 uu____1169))))
  
let exact_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____1176 =
           try
             let uu____1190 = FStar_TypeChecker_TcTerm.tc_term goal.context t
                in
             ret uu____1190
           with
           | e ->
               let uu____1203 = FStar_Syntax_Print.term_to_string t  in
               let uu____1204 = FStar_Syntax_Print.tag_of_term t  in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1203
                 uu____1204
            in
         bind uu____1176
           (fun uu____1211  ->
              match uu____1211 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp ()  in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____1224 =
                       let uu____1225 =
                         FStar_TypeChecker_Rel.is_trivial guard  in
                       Prims.op_Negation uu____1225  in
                     if uu____1224
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____1228 =
                          let uu____1235 =
                            let uu____1241 =
                              FStar_Syntax_Util.comp_to_comp_typ comp  in
                            uu____1241.FStar_Syntax_Syntax.effect_args  in
                          match uu____1235 with
                          | pre::post::uu____1250 -> ((fst pre), (fst post))
                          | uu____1280 ->
                              failwith "exact_lemma: impossible: not a lemma"
                           in
                        match uu____1228 with
                        | (pre,post) ->
                            let uu____1303 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty
                               in
                            if uu____1303
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____1306  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____1308 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____1309 =
                                 FStar_Syntax_Print.term_to_string post  in
                               let uu____1310 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty
                                  in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____1308 uu____1309 uu____1310)))))
  
let uvar_free_in_goal : FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____1319 =
          let uu____1323 = FStar_Syntax_Free.uvars g.goal_ty  in
          FStar_Util.set_elements uu____1323  in
        FStar_List.map FStar_Pervasives.fst uu____1319  in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
  
let uvar_free : FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals 
let rec __apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____1346 = let uu____1349 = exact tm  in trytac uu____1349
              in
           bind uu____1346
             (fun r  ->
                match r with
                | Some r1 -> ret ()
                | None  ->
                    let uu____1356 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm
                       in
                    (match uu____1356 with
                     | (tm1,typ,guard) ->
                         let uu____1364 =
                           let uu____1365 =
                             let uu____1366 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard
                                in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____1366
                              in
                           Prims.op_Negation uu____1365  in
                         if uu____1364
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____1369 = FStar_Syntax_Util.arrow_one typ
                               in
                            match uu____1369 with
                            | None  ->
                                let uu____1376 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                fail1 "apply: cannot unify (%s)" uu____1376
                            | Some ((bv,aq),c) ->
                                let uu____1386 =
                                  let uu____1387 =
                                    FStar_Syntax_Util.is_total_comp c  in
                                  Prims.op_Negation uu____1387  in
                                if uu____1386
                                then fail "apply: not total"
                                else
                                  (let uu____1390 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort
                                      in
                                   bind uu____1390
                                     (fun uu____1396  ->
                                        match uu____1396 with
                                        | (u,g_u) ->
                                            let tm' =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                tm1 [(u, aq)] None
                                                (goal.context).FStar_TypeChecker_Env.range
                                               in
                                            let uu____1411 = __apply uopt tm'
                                               in
                                            bind uu____1411
                                              (fun uu____1413  ->
                                                 let uu____1414 =
                                                   let uu____1415 =
                                                     let uu____1418 =
                                                       let uu____1419 =
                                                         FStar_Syntax_Util.head_and_args
                                                           u
                                                          in
                                                       fst uu____1419  in
                                                     FStar_Syntax_Subst.compress
                                                       uu____1418
                                                      in
                                                   uu____1415.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____1414 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     (uvar,uu____1438) ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____1452 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps)
                                                             in
                                                          if uu____1452
                                                          then ret ()
                                                          else
                                                            (let uu____1455 =
                                                               let uu____1457
                                                                 =
                                                                 let uu____1458
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u
                                                                    in
                                                                 let uu____1459
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                    in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____1458;
                                                                   goal_ty =
                                                                    uu____1459;
                                                                   opts =
                                                                    (goal.opts)
                                                                 }  in
                                                               [uu____1457]
                                                                in
                                                             add_goals
                                                               uu____1455))
                                                 | uu____1460 -> ret ())))))))
  
let apply : FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____1466 = __apply true tm  in focus uu____1466 
let apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1474 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm  in
         match uu____1474 with
         | (tm1,t,guard) ->
             let uu____1482 =
               let uu____1483 =
                 let uu____1484 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard
                    in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____1484
                  in
               Prims.op_Negation uu____1483  in
             if uu____1482
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____1487 = FStar_Syntax_Util.arrow_formals_comp t  in
                match uu____1487 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____1504 =
                         FStar_List.fold_left
                           (fun uu____1521  ->
                              fun uu____1522  ->
                                match (uu____1521, uu____1522) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____1571 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t
                                       in
                                    (match uu____1571 with
                                     | (u,uu____1586,g_u) ->
                                         let uu____1594 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u
                                            in
                                         (((u, aq) :: uvs), uu____1594,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs
                          in
                       match uu____1504 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs  in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp  in
                           let uu____1626 =
                             let uu____1633 =
                               let uu____1639 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1  in
                               uu____1639.FStar_Syntax_Syntax.effect_args  in
                             match uu____1633 with
                             | pre::post::uu____1648 ->
                                 ((fst pre), (fst post))
                             | uu____1678 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma"
                              in
                           (match uu____1626 with
                            | (pre,post) ->
                                let uu____1701 =
                                  let uu____1703 =
                                    FStar_Syntax_Util.mk_squash post  in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____1703 goal.goal_ty
                                   in
                                (match uu____1701 with
                                 | None  ->
                                     let uu____1705 =
                                       let uu____1706 =
                                         FStar_Syntax_Util.mk_squash post  in
                                       FStar_Syntax_Print.term_to_string
                                         uu____1706
                                        in
                                     let uu____1707 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty
                                        in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____1705 uu____1707
                                 | Some g ->
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         None
                                         (goal.context).FStar_TypeChecker_Env.range
                                        in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____1742  ->
                                               match uu____1742 with
                                               | (uu____1749,uu____1750,uu____1751,tm2,uu____1753,uu____1754)
                                                   ->
                                                   let uu____1755 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2
                                                      in
                                                   (match uu____1755 with
                                                    | (hd1,uu____1766) ->
                                                        let uu____1781 =
                                                          let uu____1782 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1
                                                             in
                                                          uu____1782.FStar_Syntax_Syntax.n
                                                           in
                                                        (match uu____1781
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____1785 ->
                                                             true
                                                         | uu____1794 ->
                                                             false))))
                                        in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____1796  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____1806 =
                                                 let uu____1810 =
                                                   FStar_Syntax_Free.uvars t1
                                                    in
                                                 FStar_Util.set_elements
                                                   uu____1810
                                                  in
                                               FStar_List.map
                                                 FStar_Pervasives.fst
                                                 uu____1806
                                                in
                                             FStar_List.existsML
                                               (fun u  ->
                                                  FStar_Syntax_Unionfind.equiv
                                                    u uv) free_uvars
                                              in
                                           let appears uv goals =
                                             FStar_List.existsML
                                               (fun g'  ->
                                                  is_free_uvar uv g'.goal_ty)
                                               goals
                                              in
                                           let checkone t1 goals =
                                             let uu____1838 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1
                                                in
                                             match uu____1838 with
                                             | (hd1,uu____1849) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____1865) ->
                                                      appears uv goals
                                                  | uu____1878 -> false)
                                              in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____1895  ->
                                                     match uu____1895 with
                                                     | (_msg,_env,_uvar,term,typ,uu____1907)
                                                         ->
                                                         let uu____1908 =
                                                           bnorm goal.context
                                                             term
                                                            in
                                                         let uu____1909 =
                                                           bnorm goal.context
                                                             typ
                                                            in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____1908;
                                                           goal_ty =
                                                             uu____1909;
                                                           opts = (goal.opts)
                                                         }))
                                              in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____1941 = f x xs1  in
                                                 if uu____1941
                                                 then
                                                   let uu____1943 =
                                                     filter' f xs1  in
                                                   x :: uu____1943
                                                 else filter' f xs1
                                              in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____1951 =
                                                      checkone g1.witness
                                                        goals
                                                       in
                                                    Prims.op_Negation
                                                      uu____1951) sub_goals
                                              in
                                           let uu____1952 =
                                             add_irrelevant_goal goal.context
                                               pre goal.opts
                                              in
                                           bind uu____1952
                                             (fun uu____1954  ->
                                                let uu____1955 =
                                                  trytac trivial  in
                                                bind uu____1955
                                                  (fun uu____1959  ->
                                                     let uu____1961 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits
                                                        in
                                                     bind uu____1961
                                                       (fun uu____1963  ->
                                                          add_goals
                                                            sub_goals1))))))))))
  
let rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____1970 =
           FStar_All.pipe_left mlog
             (fun uu____1975  ->
                let uu____1976 = FStar_Syntax_Print.bv_to_string (fst h)  in
                let uu____1977 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort
                   in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1976
                  uu____1977)
            in
         bind uu____1970
           (fun uu____1978  ->
              let uu____1979 =
                let uu____1981 =
                  let uu____1982 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h)  in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____1982  in
                FStar_Syntax_Util.destruct_typ_as_formula uu____1981  in
              match uu____1979 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____1989::(x,uu____1991)::(e,uu____1993)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2027 =
                    let uu____2028 = FStar_Syntax_Subst.compress x  in
                    uu____2028.FStar_Syntax_Syntax.n  in
                  (match uu____2027 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___96_2034 = goal  in
                         let uu____2035 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness
                            in
                         let uu____2038 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty
                            in
                         {
                           context = (uu___96_2034.context);
                           witness = uu____2035;
                           goal_ty = uu____2038;
                           opts = (uu___96_2034.opts)
                         }  in
                       replace_cur goal1
                   | uu____2041 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2042 -> fail "Not an equality hypothesis"))
  
let clear : Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2046 = FStar_TypeChecker_Env.pop_bv goal.context  in
       match uu____2046 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty  in
           let fns_tm = FStar_Syntax_Free.names goal.witness  in
           let uu____2061 = FStar_Util.set_mem x fns_ty  in
           if uu____2061
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2064 = new_uvar env' goal.goal_ty  in
              bind uu____2064
                (fun uu____2070  ->
                   match uu____2070 with
                   | (u,g) ->
                       let uu____2076 =
                         let uu____2077 =
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness u
                            in
                         Prims.op_Negation uu____2077  in
                       if uu____2076
                       then fail "clear: unification failed"
                       else
                         (let new_goal =
                            let uu___97_2081 = goal  in
                            let uu____2082 = bnorm env' u  in
                            {
                              context = env';
                              witness = uu____2082;
                              goal_ty = (uu___97_2081.goal_ty);
                              opts = (uu___97_2081.opts)
                            }  in
                          bind dismiss
                            (fun uu____2083  -> add_goals [new_goal])))))
  
let clear_hd : name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2090 = FStar_TypeChecker_Env.pop_bv goal.context  in
         match uu____2090 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
  
let revert : Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2105 = FStar_TypeChecker_Env.pop_bv goal.context  in
       match uu____2105 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2119 = FStar_Syntax_Syntax.mk_Total goal.goal_ty  in
             FStar_Syntax_Util.arrow [(x, None)] uu____2119  in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None  in
           replace_cur
             (let uu___98_2137 = goal  in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___98_2137.opts)
              }))
  
let revert_hd : name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2144 = FStar_TypeChecker_Env.pop_bv goal.context  in
         match uu____2144 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2156 = FStar_Syntax_Print.bv_to_string x  in
               let uu____2157 = FStar_Syntax_Print.bv_to_string y  in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____2156 uu____2157
             else revert)
  
let rec revert_all_hd : name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2170 = revert_all_hd xs1  in
        bind uu____2170 (fun uu____2172  -> revert_hd x)
  
let prune : Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context  in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s)
            in
         let g' =
           let uu___99_2182 = g  in
           {
             context = ctx';
             witness = (uu___99_2182.witness);
             goal_ty = (uu___99_2182.goal_ty);
             opts = (uu___99_2182.opts)
           }  in
         bind dismiss (fun uu____2183  -> add_goals [g']))
  
let addns : Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context  in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s)
            in
         let g' =
           let uu___100_2193 = g  in
           {
             context = ctx';
             witness = (uu___100_2193.witness);
             goal_ty = (uu___100_2193.goal_ty);
             opts = (uu___100_2193.opts)
           }  in
         bind dismiss (fun uu____2194  -> add_goals [g']))
  
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2224 = f x  in
      bind uu____2224
        (fun y  ->
           let uu____2228 = mapM f xs  in
           bind uu____2228 (fun ys  -> ret (y :: ys)))
  
let rec tac_bottom_fold_env :
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2260 = FStar_Syntax_Subst.compress t  in
          uu____2260.FStar_Syntax_Syntax.n  in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env  in
              let uu____2286 = ff hd1  in
              bind uu____2286
                (fun hd2  ->
                   let fa uu____2297 =
                     match uu____2297 with
                     | (a,q) ->
                         let uu____2305 = ff a  in
                         bind uu____2305 (fun a1  -> ret (a1, q))
                      in
                   let uu____2312 = mapM fa args  in
                   bind uu____2312
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2346 = FStar_Syntax_Subst.open_term bs t1  in
              (match uu____2346 with
               | (bs1,t') ->
                   let uu____2352 =
                     let uu____2354 =
                       FStar_TypeChecker_Env.push_binders env bs1  in
                     tac_bottom_fold_env f uu____2354 t'  in
                   bind uu____2352
                     (fun t''  ->
                        let uu____2356 =
                          let uu____2357 =
                            let uu____2367 =
                              FStar_Syntax_Subst.close_binders bs1  in
                            let uu____2368 = FStar_Syntax_Subst.close bs1 t''
                               in
                            (uu____2367, uu____2368, k)  in
                          FStar_Syntax_Syntax.Tm_abs uu____2357  in
                        ret uu____2356))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2382 -> ret tn  in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___101_2384 = t  in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___101_2384.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___101_2384.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___101_2384.FStar_Syntax_Syntax.vars)
                }))
  
let pointwise_rec :
  proofstate ->
    Prims.unit tac ->
      FStar_Options.optionstate ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun env  ->
          fun t  ->
            let uu____2408 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____2408 with
            | (t1,lcomp,g) ->
                let uu____2416 =
                  (let uu____2417 = FStar_Syntax_Util.is_total_lcomp lcomp
                      in
                   Prims.op_Negation uu____2417) ||
                    (let uu____2418 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____2418)
                   in
                if uu____2416
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                   let uu____2424 = new_uvar env typ  in
                   bind uu____2424
                     (fun uu____2430  ->
                        match uu____2430 with
                        | (ut,guard) ->
                            (log ps
                               (fun uu____2437  ->
                                  let uu____2438 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  let uu____2439 =
                                    FStar_Syntax_Print.term_to_string ut  in
                                  FStar_Util.print2
                                    "Pointwise_rec: making equality %s = %s\n"
                                    uu____2438 uu____2439);
                             (let uu____2440 =
                                let uu____2442 =
                                  let uu____2443 =
                                    FStar_TypeChecker_TcTerm.universe_of env
                                      typ
                                     in
                                  FStar_Syntax_Util.mk_eq2 uu____2443 typ t1
                                    ut
                                   in
                                add_irrelevant_goal env uu____2442 opts  in
                              bind uu____2440
                                (fun uu____2444  ->
                                   let uu____2445 =
                                     bind tau
                                       (fun uu____2447  ->
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env guard;
                                          (let ut1 =
                                             FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                               env ut
                                              in
                                           ret ut1))
                                      in
                                   focus uu____2445)))))
  
let pointwise : Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2458 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals"  in
         match uu____2458 with
         | (g,gs) ->
             let gt1 = g.goal_ty  in
             (log ps
                (fun uu____2479  ->
                   let uu____2480 = FStar_Syntax_Print.term_to_string gt1  in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2480);
              bind dismiss_all
                (fun uu____2481  ->
                   let uu____2482 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1
                      in
                   bind uu____2482
                     (fun gt'  ->
                        log ps
                          (fun uu____2486  ->
                             let uu____2487 =
                               FStar_Syntax_Print.term_to_string gt'  in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2487);
                        (let uu____2488 = push_goals gs  in
                         bind uu____2488
                           (fun uu____2490  ->
                              add_goals
                                [(let uu___102_2491 = g  in
                                  {
                                    context = (uu___102_2491.context);
                                    witness = (uu___102_2491.witness);
                                    goal_ty = gt';
                                    opts = (uu___102_2491.opts)
                                  })]))))))
  
let trefl : Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2494 = FStar_Syntax_Util.un_squash g.goal_ty  in
       match uu____2494 with
       | Some t ->
           let uu____2504 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____2504 with
            | (hd1,args) ->
                let uu____2525 =
                  let uu____2533 =
                    let uu____2534 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____2534.FStar_Syntax_Syntax.n  in
                  (uu____2533, args)  in
                (match uu____2525 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2544::(l,uu____2546)::(r,uu____2548)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.eq2_lid
                     ->
                     let l1 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.Delta_constant;
                         FStar_TypeChecker_Normalize.UnfoldTac] g.context l
                        in
                     let r1 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.Delta_constant;
                         FStar_TypeChecker_Normalize.UnfoldTac] g.context r
                        in
                     let uu____2584 =
                       let uu____2585 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l1 r1  in
                       Prims.op_Negation uu____2585  in
                     if uu____2584
                     then
                       let uu____2587 = FStar_Syntax_Print.term_to_string l1
                          in
                       let uu____2588 = FStar_Syntax_Print.term_to_string r1
                          in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____2587 uu____2588
                     else (solve g FStar_Syntax_Const.exp_unit; dismiss)
                 | (hd2,uu____2592) ->
                     let uu____2603 = FStar_Syntax_Print.term_to_string t  in
                     fail1 "trefl: not an equality (%s)" uu____2603))
       | None  -> fail "not an irrelevant goal")
  
let flip : Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___103_2613 = ps  in
              {
                main_context = (uu___103_2613.main_context);
                main_goal = (uu___103_2613.main_goal);
                all_implicits = (uu___103_2613.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___103_2613.smt_goals)
              })
       | uu____2614 -> fail "flip: less than 2 goals")
  
let later : Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___104_2622 = ps  in
              {
                main_context = (uu___104_2622.main_context);
                main_goal = (uu___104_2622.main_goal);
                all_implicits = (uu___104_2622.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___104_2622.smt_goals)
              }))
  
let qed : Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2626 -> fail "Not done!")
  
let cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2640 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t  in
         match uu____2640 with
         | (t1,typ,guard) ->
             let uu____2650 = FStar_Syntax_Util.head_and_args typ  in
             (match uu____2650 with
              | (hd1,args) ->
                  let uu____2679 =
                    let uu____2687 =
                      let uu____2688 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____2688.FStar_Syntax_Syntax.n  in
                    (uu____2687, args)  in
                  (match uu____2679 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2701)::(q,uu____2703)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p  in
                       let v_q = FStar_Syntax_Syntax.new_bv None q  in
                       let g1 =
                         let uu___105_2732 = g  in
                         let uu____2733 =
                           FStar_TypeChecker_Env.push_bv g.context v_p  in
                         {
                           context = uu____2733;
                           witness = (uu___105_2732.witness);
                           goal_ty = (uu___105_2732.goal_ty);
                           opts = (uu___105_2732.opts)
                         }  in
                       let g2 =
                         let uu___106_2735 = g  in
                         let uu____2736 =
                           FStar_TypeChecker_Env.push_bv g.context v_q  in
                         {
                           context = uu____2736;
                           witness = (uu___106_2735.witness);
                           goal_ty = (uu___106_2735.goal_ty);
                           opts = (uu___106_2735.opts)
                         }  in
                       bind dismiss
                         (fun uu____2739  ->
                            let uu____2740 = add_goals [g1; g2]  in
                            bind uu____2740
                              (fun uu____2744  ->
                                 let uu____2745 =
                                   let uu____2748 =
                                     FStar_Syntax_Syntax.bv_to_name v_p  in
                                   let uu____2749 =
                                     FStar_Syntax_Syntax.bv_to_name v_q  in
                                   (uu____2748, uu____2749)  in
                                 ret uu____2745))
                   | uu____2752 ->
                       let uu____2760 = FStar_Syntax_Print.term_to_string typ
                          in
                       fail1 "Not a disjunction: %s" uu____2760)))
  
let set_options : Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____2771 = FStar_Util.smap_copy g.opts  in
          FStar_Options.set uu____2771);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___107_2777 = g  in
                 {
                   context = (uu___107_2777.context);
                   witness = (uu___107_2777.witness);
                   goal_ty = (uu___107_2777.goal_ty);
                   opts = opts'
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err1 ->
               fail2 "Setting options `%s` failed: %s" s err1
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let cur_env : env tac =
  bind cur_goal (fun g  -> FStar_All.pipe_left ret g.context) 
let cur_goal' : FStar_Syntax_Syntax.typ tac =
  bind cur_goal (fun g  -> FStar_All.pipe_left ret g.goal_ty) 
let cur_witness : FStar_Syntax_Syntax.term tac =
  bind cur_goal (fun g  -> FStar_All.pipe_left ret g.witness) 
let proofstate_of_goal_ty :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> (proofstate * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      let uu____2800 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____2800 with
      | (u,uu____2810,g_u) ->
          let g =
            let uu____2819 = FStar_Options.peek ()  in
            { context = env; witness = u; goal_ty = typ; opts = uu____2819 }
             in
          let ps =
            {
              main_context = env;
              main_goal = g;
              all_implicits = (g_u.FStar_TypeChecker_Env.implicits);
              goals = [g];
              smt_goals = []
            }  in
          (ps, u)
  