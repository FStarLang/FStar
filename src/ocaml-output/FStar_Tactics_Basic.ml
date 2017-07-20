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
let __proj__Mkgoal__item__context : goal -> env =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} ->
        __fname__context
  
let __proj__Mkgoal__item__witness : goal -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} ->
        __fname__witness
  
let __proj__Mkgoal__item__goal_ty : goal -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} ->
        __fname__goal_ty
  
let __proj__Mkgoal__item__opts : goal -> FStar_Options.optionstate =
  fun projectee  ->
    match projectee with
    | { context = __fname__context; witness = __fname__witness;
        goal_ty = __fname__goal_ty; opts = __fname__opts;_} -> __fname__opts
  
type proofstate =
  {
  main_context: env ;
  main_goal: goal ;
  all_implicits: implicits ;
  goals: goal Prims.list ;
  smt_goals: goal Prims.list }
let __proj__Mkproofstate__item__main_context : proofstate -> env =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__main_context
  
let __proj__Mkproofstate__item__main_goal : proofstate -> goal =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__main_goal
  
let __proj__Mkproofstate__item__all_implicits : proofstate -> implicits =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__all_implicits
  
let __proj__Mkproofstate__item__goals : proofstate -> goal Prims.list =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__goals
  
let __proj__Mkproofstate__item__smt_goals : proofstate -> goal Prims.list =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals;_} -> __fname__smt_goals
  
type 'a result =
  | Success of ('a,proofstate) FStar_Pervasives_Native.tuple2 
  | Failed of (Prims.string,proofstate) FStar_Pervasives_Native.tuple2 
let uu___is_Success : 'a . 'a result -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____195 -> false
  
let __proj__Success__item___0 :
  'a . 'a result -> ('a,proofstate) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Success _0 -> _0 
let uu___is_Failed : 'a . 'a result -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____241 -> false
  
let __proj__Failed__item___0 :
  'a . 'a result -> (Prims.string,proofstate) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Failed _0 -> _0 
exception TacFailure of Prims.string 
let uu___is_TacFailure : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | TacFailure uu____276 -> true | uu____277 -> false
  
let __proj__TacFailure__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | TacFailure uu____285 -> uu____285 
type 'a tac = {
  tac_f: proofstate -> 'a result }
let __proj__Mktac__item__tac_f : 'a . 'a tac -> proofstate -> 'a result =
  fun projectee  ->
    match projectee with | { tac_f = __fname__tac_f;_} -> __fname__tac_f
  
let mk_tac : 'a . (proofstate -> 'a result) -> 'a tac =
  fun f  -> { tac_f = f } 
let run : 'Auu____349 . 'Auu____349 tac -> proofstate -> 'Auu____349 result =
  fun t  -> fun p  -> t.tac_f p 
let ret : 'a . 'a -> 'a tac = fun x  -> mk_tac (fun p  -> Success (x, p)) 
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____416 = run t1 p  in
           match uu____416 with
           | Success (a,q) -> let uu____423 = t2 a  in run uu____423 q
           | Failed (msg,q) -> Failed (msg, q))
  
let idtac : Prims.unit tac = ret () 
let goal_to_string : goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____435 = FStar_TypeChecker_Env.all_binders g.context  in
      FStar_All.pipe_right uu____435
        (FStar_Syntax_Print.binders_to_string ", ")
       in
    let uu____436 = FStar_Syntax_Print.term_to_string g.witness  in
    let uu____437 = FStar_Syntax_Print.term_to_string g.goal_ty  in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____436 uu____437
  
let tacprint : Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let tacprint1 : Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____450 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____450
  
let tacprint2 : Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____463 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____463
  
let tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____480 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____480
  
let comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____486) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____496) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let is_irrelevant : goal -> Prims.bool =
  fun g  ->
    let uu____510 =
      let uu____515 =
        FStar_TypeChecker_Normalize.unfold_whnf g.context g.goal_ty  in
      FStar_Syntax_Util.un_squash uu____515  in
    match uu____510 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____521 -> false
  
let dump_goal : 'Auu____532 . 'Auu____532 -> goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____542 = goal_to_string goal  in tacprint uu____542
  
let dump_cur : proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____552 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____556 = FStar_List.hd ps.goals  in dump_goal ps uu____556))
  
let dump_proofstate : proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____568 = FStar_Util.string_of_int (FStar_List.length ps.goals)
          in
       tacprint1 "ACTIVE goals (%s):" uu____568);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____571 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals)  in
       tacprint1 "SMT goals (%s):" uu____571);
      FStar_List.iter (dump_goal ps) ps.smt_goals
  
let print_proof_state1 : Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_cur p msg; Success ((), p)) 
let print_proof_state : Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p)) 
let get : proofstate tac = mk_tac (fun p  -> Success (p, p)) 
let tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec log : proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun ps  ->
    fun f  ->
      let uu____621 = FStar_ST.read tac_verb_dbg  in
      match uu____621 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____627 =
              let uu____630 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____630  in
            FStar_ST.write tac_verb_dbg uu____627);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog : (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ()) 
let fail : 'Auu____654 . Prims.string -> 'Auu____654 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____665 =
            FStar_TypeChecker_Env.debug ps.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____665
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         Failed (msg, ps))
  
let fail1 : 'Auu____673 . Prims.string -> Prims.string -> 'Auu____673 tac =
  fun msg  ->
    fun x  -> let uu____684 = FStar_Util.format1 msg x  in fail uu____684
  
let fail2 :
  'Auu____693 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____693 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____708 = FStar_Util.format2 msg x y  in fail uu____708
  
let fail3 :
  'Auu____719 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____719 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____738 = FStar_Util.format3 msg x y z  in fail uu____738
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____766 = run t ps  in
         match uu____766 with
         | Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              Success ((FStar_Pervasives_Native.Some a), q))
         | Failed (uu____780,uu____781) ->
             (FStar_Syntax_Unionfind.rollback tx;
              Success (FStar_Pervasives_Native.None, ps)))
  
let set : proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____796  -> Success ((), p)) 
let solve : goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____805 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution
         in
      if uu____805
      then ()
      else
        (let uu____807 =
           let uu____808 =
             let uu____809 = FStar_Syntax_Print.term_to_string solution  in
             let uu____810 = FStar_Syntax_Print.term_to_string goal.witness
                in
             let uu____811 = FStar_Syntax_Print.term_to_string goal.goal_ty
                in
             FStar_Util.format3 "%s does not solve %s : %s" uu____809
               uu____810 uu____811
              in
           TacFailure uu____808  in
         raise uu____807)
  
let dismiss : Prims.unit tac =
  bind get
    (fun p  ->
       let uu____817 =
         let uu___82_818 = p  in
         let uu____819 = FStar_List.tl p.goals  in
         {
           main_context = (uu___82_818.main_context);
           main_goal = (uu___82_818.main_goal);
           all_implicits = (uu___82_818.all_implicits);
           goals = uu____819;
           smt_goals = (uu___82_818.smt_goals)
         }  in
       set uu____817)
  
let dismiss_all : Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___83_828 = p  in
          {
            main_context = (uu___83_828.main_context);
            main_goal = (uu___83_828.main_goal);
            all_implicits = (uu___83_828.all_implicits);
            goals = [];
            smt_goals = (uu___83_828.smt_goals)
          }))
  
let add_goals : goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___84_845 = p  in
            {
              main_context = (uu___84_845.main_context);
              main_goal = (uu___84_845.main_goal);
              all_implicits = (uu___84_845.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___84_845.smt_goals)
            }))
  
let add_smt_goals : goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___85_862 = p  in
            {
              main_context = (uu___85_862.main_context);
              main_goal = (uu___85_862.main_goal);
              all_implicits = (uu___85_862.all_implicits);
              goals = (uu___85_862.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
  
let push_goals : goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___86_879 = p  in
            {
              main_context = (uu___86_879.main_context);
              main_goal = (uu___86_879.main_goal);
              all_implicits = (uu___86_879.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___86_879.smt_goals)
            }))
  
let push_smt_goals : goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___87_896 = p  in
            {
              main_context = (uu___87_896.main_context);
              main_goal = (uu___87_896.main_goal);
              all_implicits = (uu___87_896.all_implicits);
              goals = (uu___87_896.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
  
let replace_cur : goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____906  -> add_goals [g]) 
let add_implicits : implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___88_919 = p  in
            {
              main_context = (uu___88_919.main_context);
              main_goal = (uu___88_919.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___88_919.goals);
              smt_goals = (uu___88_919.smt_goals)
            }))
  
let new_uvar :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2 tac
  =
  fun env  ->
    fun typ  ->
      let uu____952 =
        FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____952 with
      | (u,uu____972,g_u) ->
          let uu____986 = add_implicits g_u.FStar_TypeChecker_Env.implicits
             in
          bind uu____986 (fun uu____994  -> ret (u, g_u))
  
let is_true : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1003 = FStar_Syntax_Util.un_squash t  in
    match uu____1003 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1013 =
          let uu____1014 = FStar_Syntax_Subst.compress t'  in
          uu____1014.FStar_Syntax_Syntax.n  in
        (match uu____1013 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1018 -> false)
    | uu____1019 -> false
  
let is_false : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1028 = FStar_Syntax_Util.un_squash t  in
    match uu____1028 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1038 =
          let uu____1039 = FStar_Syntax_Subst.compress t'  in
          uu____1039.FStar_Syntax_Syntax.n  in
        (match uu____1038 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1043 -> false)
    | uu____1044 -> false
  
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
        let uu____1078 = new_uvar env typ  in
        bind uu____1078
          (fun uu____1093  ->
             match uu____1093 with
             | (u,g_u) ->
                 let goal =
                   { context = env; witness = u; goal_ty = typ; opts }  in
                 add_goals [goal])
  
let smt : Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1108 = is_irrelevant g  in
       if uu____1108
       then bind dismiss (fun uu____1112  -> add_smt_goals [g])
       else
         (let uu____1114 = FStar_Syntax_Print.term_to_string g.goal_ty  in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1114))
  
let divide :
  'a 'b .
    Prims.int ->
      'a tac -> 'b tac -> ('a,'b) FStar_Pervasives_Native.tuple2 tac
  =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____1160 =
               try
                 let uu____1194 = FStar_List.splitAt n1 p.goals  in
                 ret uu____1194
               with | uu____1224 -> fail "divide: not enough goals"  in
             bind uu____1160
               (fun uu____1251  ->
                  match uu____1251 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___89_1277 = p  in
                        {
                          main_context = (uu___89_1277.main_context);
                          main_goal = (uu___89_1277.main_goal);
                          all_implicits = (uu___89_1277.all_implicits);
                          goals = lgs;
                          smt_goals = []
                        }  in
                      let rp =
                        let uu___90_1279 = p  in
                        {
                          main_context = (uu___90_1279.main_context);
                          main_goal = (uu___90_1279.main_goal);
                          all_implicits = (uu___90_1279.all_implicits);
                          goals = rgs;
                          smt_goals = []
                        }  in
                      let uu____1280 = set lp  in
                      bind uu____1280
                        (fun uu____1288  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1302 = set rp  in
                                     bind uu____1302
                                       (fun uu____1310  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___91_1326 = p
                                                         in
                                                      {
                                                        main_context =
                                                          (uu___91_1326.main_context);
                                                        main_goal =
                                                          (uu___91_1326.main_goal);
                                                        all_implicits =
                                                          (uu___91_1326.all_implicits);
                                                        goals =
                                                          (FStar_List.append
                                                             lp'.goals
                                                             rp'.goals);
                                                        smt_goals =
                                                          (FStar_List.append
                                                             lp'.smt_goals
                                                             (FStar_List.append
                                                                rp'.smt_goals
                                                                p.smt_goals))
                                                      }  in
                                                    let uu____1327 = set p'
                                                       in
                                                    bind uu____1327
                                                      (fun uu____1335  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1355 = divide (Prims.parse_int "1") f idtac  in
    bind uu____1355
      (fun uu____1368  -> match uu____1368 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.goals with
         | [] -> ret []
         | uu____1403::uu____1404 ->
             let uu____1407 =
               let uu____1416 = map tau  in
               divide (Prims.parse_int "1") tau uu____1416  in
             bind uu____1407
               (fun uu____1434  ->
                  match uu____1434 with | (h,t) -> ret (h :: t)))
  
let seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____1473 =
        bind t1
          (fun uu____1478  ->
             let uu____1479 = map t2  in
             bind uu____1479 (fun uu____1487  -> ret ()))
         in
      focus uu____1473
  
let intro :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 tac
  =
  bind cur_goal
    (fun goal  ->
       let uu____1510 = FStar_Syntax_Util.arrow_one goal.goal_ty  in
       match uu____1510 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1529 = FStar_Syntax_Subst.open_comp [b] c  in
           (match uu____1529 with
            | (bs,c1) ->
                let b1 =
                  match bs with
                  | b1::[] -> b1
                  | uu____1564 ->
                      failwith
                        "impossible: open_comp returned different amount of binders"
                   in
                let uu____1569 =
                  let uu____1570 = FStar_Syntax_Util.is_total_comp c1  in
                  Prims.op_Negation uu____1570  in
                if uu____1569
                then fail "Codomain is effectful"
                else
                  (let env' =
                     FStar_TypeChecker_Env.push_binders goal.context [b1]  in
                   let typ' = comp_to_typ c1  in
                   let uu____1592 = new_uvar env' typ'  in
                   bind uu____1592
                     (fun uu____1612  ->
                        match uu____1612 with
                        | (u,g) ->
                            let uu____1625 =
                              let uu____1626 =
                                FStar_Syntax_Util.abs [b1] u
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                goal.witness uu____1626
                               in
                            if uu____1625
                            then
                              let uu____1641 =
                                let uu____1644 =
                                  let uu___94_1645 = goal  in
                                  let uu____1646 = bnorm env' u  in
                                  let uu____1647 = bnorm env' typ'  in
                                  {
                                    context = env';
                                    witness = uu____1646;
                                    goal_ty = uu____1647;
                                    opts = (uu___94_1645.opts)
                                  }  in
                                replace_cur uu____1644  in
                              bind uu____1641 (fun uu____1653  -> ret b1)
                            else fail "intro: unification failed")))
       | FStar_Pervasives_Native.None  ->
           let uu____1667 = FStar_Syntax_Print.term_to_string goal.goal_ty
              in
           fail1 "intro: goal is not an arrow (%s)" uu____1667)
  
let intro_rec :
  (FStar_Syntax_Syntax.binder,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 tac
  =
  bind cur_goal
    (fun goal  ->
       FStar_Util.print_string
         "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
       FStar_Util.print_string
         "WARNING (intro_rec): proceed at your own risk...\n";
       (let uu____1704 = FStar_Syntax_Util.arrow_one goal.goal_ty  in
        match uu____1704 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____1727 = FStar_Syntax_Subst.open_comp [b] c  in
            (match uu____1727 with
             | (bs,c1) ->
                 let b1 =
                   match bs with
                   | b1::[] -> b1
                   | uu____1766 ->
                       failwith
                         "impossible: open_comp returned different amount of binders"
                    in
                 let uu____1771 =
                   let uu____1772 = FStar_Syntax_Util.is_total_comp c1  in
                   Prims.op_Negation uu____1772  in
                 if uu____1771
                 then fail "Codomain is effectful"
                 else
                   (let bv =
                      FStar_Syntax_Syntax.gen_bv "__recf"
                        FStar_Pervasives_Native.None goal.goal_ty
                       in
                    let bs1 =
                      let uu____1796 = FStar_Syntax_Syntax.mk_binder bv  in
                      [uu____1796; b1]  in
                    let env' =
                      FStar_TypeChecker_Env.push_binders goal.context bs1  in
                    let uu____1806 =
                      let uu____1813 = comp_to_typ c1  in
                      new_uvar env' uu____1813  in
                    bind uu____1806
                      (fun uu____1838  ->
                         match uu____1838 with
                         | (u,g) ->
                             let lb =
                               let uu____1856 =
                                 FStar_Syntax_Util.abs [b1] u
                                   FStar_Pervasives_Native.None
                                  in
                               FStar_Syntax_Util.mk_letbinding
                                 (FStar_Util.Inl bv) [] goal.goal_ty
                                 FStar_Parser_Const.effect_Tot_lid uu____1856
                                in
                             let body = FStar_Syntax_Syntax.bv_to_name bv  in
                             let uu____1868 =
                               FStar_Syntax_Subst.close_let_rec [lb] body  in
                             (match uu____1868 with
                              | (lbs,body1) ->
                                  let tm =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((true, lbs), body1))
                                      FStar_Pervasives_Native.None
                                      (goal.witness).FStar_Syntax_Syntax.pos
                                     in
                                  (FStar_Util.print_string
                                     "calling teq_nosmt\n";
                                   (let res =
                                      FStar_TypeChecker_Rel.teq_nosmt
                                        goal.context goal.witness tm
                                       in
                                    if res
                                    then
                                      let uu____1914 =
                                        let uu____1917 =
                                          let uu___95_1918 = goal  in
                                          let uu____1919 = bnorm env' u  in
                                          let uu____1920 =
                                            let uu____1921 = comp_to_typ c1
                                               in
                                            bnorm env' uu____1921  in
                                          {
                                            context = env';
                                            witness = uu____1919;
                                            goal_ty = uu____1920;
                                            opts = (uu___95_1918.opts)
                                          }  in
                                        replace_cur uu____1917  in
                                      bind uu____1914
                                        (fun uu____1932  ->
                                           let uu____1933 =
                                             let uu____1942 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 bv
                                                in
                                             (uu____1942, b1)  in
                                           ret uu____1933)
                                    else fail "intro_rec: unification failed"))))))
        | FStar_Pervasives_Native.None  ->
            let uu____1968 = FStar_Syntax_Print.term_to_string goal.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____1968))
  
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
           let uu____2006 =
             let uu____2009 = FStar_List.map tr s  in
             FStar_List.flatten uu____2009  in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2006
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
           (let uu___96_2020 = goal  in
            {
              context = (uu___96_2020.context);
              witness = w;
              goal_ty = t;
              opts = (uu___96_2020.opts)
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
       let uu____2039 = istrivial goal.context goal.goal_ty  in
       if uu____2039
       then (solve goal FStar_Syntax_Util.exp_unit; dismiss)
       else
         (let uu____2044 = FStar_Syntax_Print.term_to_string goal.goal_ty  in
          fail1 "Not a trivial goal: %s" uu____2044))
  
let exact : FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2056 =
           try
             let uu____2084 =
               (goal.context).FStar_TypeChecker_Env.type_of goal.context t
                in
             ret uu____2084
           with
           | e ->
               let uu____2111 = FStar_Syntax_Print.term_to_string t  in
               let uu____2112 = FStar_Syntax_Print.tag_of_term t  in
               fail2 "exact: term is not typeable: %s (%s)" uu____2111
                 uu____2112
            in
         bind uu____2056
           (fun uu____2130  ->
              match uu____2130 with
              | (t1,typ,guard) ->
                  let uu____2142 =
                    let uu____2143 =
                      let uu____2144 =
                        FStar_TypeChecker_Rel.discharge_guard goal.context
                          guard
                         in
                      FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                        uu____2144
                       in
                    Prims.op_Negation uu____2143  in
                  if uu____2142
                  then fail "exact: got non-trivial guard"
                  else
                    (let uu____2148 =
                       FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                         goal.goal_ty
                        in
                     if uu____2148
                     then (solve goal t1; dismiss)
                     else
                       (let uu____2153 = FStar_Syntax_Print.term_to_string t1
                           in
                        let uu____2154 =
                          let uu____2155 = bnorm goal.context typ  in
                          FStar_Syntax_Print.term_to_string uu____2155  in
                        let uu____2156 =
                          FStar_Syntax_Print.term_to_string goal.goal_ty  in
                        fail3 "%s : %s does not exactly solve the goal %s"
                          uu____2153 uu____2154 uu____2156))))
  
let exact_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         let uu____2168 =
           try
             let uu____2196 = FStar_TypeChecker_TcTerm.tc_term goal.context t
                in
             ret uu____2196
           with
           | e ->
               let uu____2223 = FStar_Syntax_Print.term_to_string t  in
               let uu____2224 = FStar_Syntax_Print.tag_of_term t  in
               fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2223
                 uu____2224
            in
         bind uu____2168
           (fun uu____2242  ->
              match uu____2242 with
              | (t1,lcomp,guard) ->
                  let comp = lcomp.FStar_Syntax_Syntax.comp ()  in
                  if Prims.op_Negation (FStar_Syntax_Util.is_lemma_comp comp)
                  then fail "exact_lemma: not a lemma"
                  else
                    (let uu____2260 =
                       let uu____2261 =
                         FStar_TypeChecker_Rel.is_trivial guard  in
                       Prims.op_Negation uu____2261  in
                     if uu____2260
                     then fail "exact: got non-trivial guard"
                     else
                       (let uu____2265 =
                          let uu____2274 =
                            let uu____2283 =
                              FStar_Syntax_Util.comp_to_comp_typ comp  in
                            uu____2283.FStar_Syntax_Syntax.effect_args  in
                          match uu____2274 with
                          | pre::post::uu____2294 ->
                              ((FStar_Pervasives_Native.fst pre),
                                (FStar_Pervasives_Native.fst post))
                          | uu____2335 ->
                              failwith "exact_lemma: impossible: not a lemma"
                           in
                        match uu____2265 with
                        | (pre,post) ->
                            let uu____2364 =
                              FStar_TypeChecker_Rel.teq_nosmt goal.context
                                post goal.goal_ty
                               in
                            if uu____2364
                            then
                              (solve goal t1;
                               bind dismiss
                                 (fun uu____2369  ->
                                    add_irrelevant_goal goal.context pre
                                      goal.opts))
                            else
                              (let uu____2371 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____2372 =
                                 FStar_Syntax_Print.term_to_string post  in
                               let uu____2373 =
                                 FStar_Syntax_Print.term_to_string
                                   goal.goal_ty
                                  in
                               fail3
                                 "%s : %s does not exactly solve the goal %s"
                                 uu____2371 uu____2372 uu____2373)))))
  
let uvar_free_in_goal : FStar_Syntax_Syntax.uvar -> goal -> Prims.bool =
  fun u  ->
    fun g  ->
      let free_uvars =
        let uu____2385 =
          let uu____2392 = FStar_Syntax_Free.uvars g.goal_ty  in
          FStar_Util.set_elements uu____2392  in
        FStar_List.map FStar_Pervasives_Native.fst uu____2385  in
      FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars
  
let uvar_free : FStar_Syntax_Syntax.uvar -> proofstate -> Prims.bool =
  fun u  -> fun ps  -> FStar_List.existsML (uvar_free_in_goal u) ps.goals 
let rec __apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      bind cur_goal
        (fun goal  ->
           let uu____2430 = let uu____2435 = exact tm  in trytac uu____2435
              in
           bind uu____2430
             (fun r  ->
                match r with
                | FStar_Pervasives_Native.Some r1 -> ret ()
                | FStar_Pervasives_Native.None  ->
                    let uu____2448 =
                      (goal.context).FStar_TypeChecker_Env.type_of
                        goal.context tm
                       in
                    (match uu____2448 with
                     | (tm1,typ,guard) ->
                         let uu____2460 =
                           let uu____2461 =
                             let uu____2462 =
                               FStar_TypeChecker_Rel.discharge_guard
                                 goal.context guard
                                in
                             FStar_All.pipe_left
                               FStar_TypeChecker_Rel.is_trivial uu____2462
                              in
                           Prims.op_Negation uu____2461  in
                         if uu____2460
                         then fail "apply: got non-trivial guard"
                         else
                           (let uu____2466 = FStar_Syntax_Util.arrow_one typ
                               in
                            match uu____2466 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____2479 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                fail1 "apply: cannot unify (%s)" uu____2479
                            | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                let uu____2495 =
                                  let uu____2496 =
                                    FStar_Syntax_Util.is_total_comp c  in
                                  Prims.op_Negation uu____2496  in
                                if uu____2495
                                then fail "apply: not total"
                                else
                                  (let uu____2500 =
                                     new_uvar goal.context
                                       bv.FStar_Syntax_Syntax.sort
                                      in
                                   bind uu____2500
                                     (fun uu____2516  ->
                                        match uu____2516 with
                                        | (u,g_u) ->
                                            let tm' =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                tm1 [(u, aq)]
                                                FStar_Pervasives_Native.None
                                                (goal.context).FStar_TypeChecker_Env.range
                                               in
                                            let uu____2536 = __apply uopt tm'
                                               in
                                            bind uu____2536
                                              (fun uu____2543  ->
                                                 let uu____2544 =
                                                   let uu____2545 =
                                                     let uu____2548 =
                                                       let uu____2549 =
                                                         FStar_Syntax_Util.head_and_args
                                                           u
                                                          in
                                                       FStar_Pervasives_Native.fst
                                                         uu____2549
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____2548
                                                      in
                                                   uu____2545.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____2544 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     (uvar,uu____2577) ->
                                                     bind get
                                                       (fun ps  ->
                                                          let uu____2605 =
                                                            uopt &&
                                                              (uvar_free uvar
                                                                 ps)
                                                             in
                                                          if uu____2605
                                                          then ret ()
                                                          else
                                                            (let uu____2609 =
                                                               let uu____2612
                                                                 =
                                                                 let uu____2613
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    u
                                                                    in
                                                                 let uu____2614
                                                                   =
                                                                   bnorm
                                                                    goal.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                    in
                                                                 {
                                                                   context =
                                                                    (goal.context);
                                                                   witness =
                                                                    uu____2613;
                                                                   goal_ty =
                                                                    uu____2614;
                                                                   opts =
                                                                    (goal.opts)
                                                                 }  in
                                                               [uu____2612]
                                                                in
                                                             add_goals
                                                               uu____2609))
                                                 | uu____2615 -> ret ())))))))
  
let apply : FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  -> let uu____2624 = __apply true tm  in focus uu____2624 
let apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____2642 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm  in
         match uu____2642 with
         | (tm1,t,guard) ->
             let uu____2654 =
               let uu____2655 =
                 let uu____2656 =
                   FStar_TypeChecker_Rel.discharge_guard goal.context guard
                    in
                 FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial
                   uu____2656
                  in
               Prims.op_Negation uu____2655  in
             if uu____2654
             then fail "apply_lemma: got non-trivial guard"
             else
               (let uu____2660 = FStar_Syntax_Util.arrow_formals_comp t  in
                match uu____2660 with
                | (bs,comp) ->
                    if
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_lemma_comp comp)
                    then fail "apply_lemma: not a lemma"
                    else
                      (let uu____2690 =
                         FStar_List.fold_left
                           (fun uu____2736  ->
                              fun uu____2737  ->
                                match (uu____2736, uu____2737) with
                                | ((uvs,guard1,subst1),(b,aq)) ->
                                    let b_t =
                                      FStar_Syntax_Subst.subst subst1
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____2828 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "apply_lemma"
                                        (goal.goal_ty).FStar_Syntax_Syntax.pos
                                        goal.context b_t
                                       in
                                    (match uu____2828 with
                                     | (u,uu____2856,g_u) ->
                                         let uu____2870 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 g_u
                                            in
                                         (((u, aq) :: uvs), uu____2870,
                                           ((FStar_Syntax_Syntax.NT (b, u))
                                           :: subst1)))) ([], guard, []) bs
                          in
                       match uu____2690 with
                       | (uvs,implicits,subst1) ->
                           let uvs1 = FStar_List.rev uvs  in
                           let comp1 =
                             FStar_Syntax_Subst.subst_comp subst1 comp  in
                           let uu____2928 =
                             let uu____2937 =
                               let uu____2946 =
                                 FStar_Syntax_Util.comp_to_comp_typ comp1  in
                               uu____2946.FStar_Syntax_Syntax.effect_args  in
                             match uu____2937 with
                             | pre::post::uu____2957 ->
                                 ((FStar_Pervasives_Native.fst pre),
                                   (FStar_Pervasives_Native.fst post))
                             | uu____2998 ->
                                 failwith
                                   "apply_lemma: impossible: not a lemma"
                              in
                           (match uu____2928 with
                            | (pre,post) ->
                                let uu____3027 =
                                  let uu____3030 =
                                    FStar_Syntax_Util.mk_squash post  in
                                  FStar_TypeChecker_Rel.try_teq false
                                    goal.context uu____3030 goal.goal_ty
                                   in
                                (match uu____3027 with
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____3033 =
                                       let uu____3034 =
                                         FStar_Syntax_Util.mk_squash post  in
                                       FStar_Syntax_Print.term_to_string
                                         uu____3034
                                        in
                                     let uu____3035 =
                                       FStar_Syntax_Print.term_to_string
                                         goal.goal_ty
                                        in
                                     fail2
                                       "apply_lemma: does not unify with goal: %s vs %s"
                                       uu____3033 uu____3035
                                 | FStar_Pervasives_Native.Some g ->
                                     let uu____3037 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         goal.context g
                                        in
                                     let solution =
                                       FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                         FStar_Pervasives_Native.None
                                         (goal.context).FStar_TypeChecker_Env.range
                                        in
                                     let implicits1 =
                                       FStar_All.pipe_right
                                         implicits.FStar_TypeChecker_Env.implicits
                                         (FStar_List.filter
                                            (fun uu____3108  ->
                                               match uu____3108 with
                                               | (uu____3121,uu____3122,uu____3123,tm2,uu____3125,uu____3126)
                                                   ->
                                                   let uu____3127 =
                                                     FStar_Syntax_Util.head_and_args
                                                       tm2
                                                      in
                                                   (match uu____3127 with
                                                    | (hd1,uu____3143) ->
                                                        let uu____3164 =
                                                          let uu____3165 =
                                                            FStar_Syntax_Subst.compress
                                                              hd1
                                                             in
                                                          uu____3165.FStar_Syntax_Syntax.n
                                                           in
                                                        (match uu____3164
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_uvar
                                                             uu____3168 ->
                                                             true
                                                         | uu____3185 ->
                                                             false))))
                                        in
                                     (solve goal solution;
                                      bind dismiss
                                        (fun uu____3195  ->
                                           let is_free_uvar uv t1 =
                                             let free_uvars =
                                               let uu____3206 =
                                                 let uu____3213 =
                                                   FStar_Syntax_Free.uvars t1
                                                    in
                                                 FStar_Util.set_elements
                                                   uu____3213
                                                  in
                                               FStar_List.map
                                                 FStar_Pervasives_Native.fst
                                                 uu____3206
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
                                             let uu____3254 =
                                               FStar_Syntax_Util.head_and_args
                                                 t1
                                                in
                                             match uu____3254 with
                                             | (hd1,uu____3270) ->
                                                 (match hd1.FStar_Syntax_Syntax.n
                                                  with
                                                  | FStar_Syntax_Syntax.Tm_uvar
                                                      (uv,uu____3292) ->
                                                      appears uv goals
                                                  | uu____3317 -> false)
                                              in
                                           let sub_goals =
                                             FStar_All.pipe_right implicits1
                                               (FStar_List.map
                                                  (fun uu____3358  ->
                                                     match uu____3358 with
                                                     | (_msg,_env,_uvar,term,typ,uu____3376)
                                                         ->
                                                         let uu____3377 =
                                                           bnorm goal.context
                                                             term
                                                            in
                                                         let uu____3378 =
                                                           bnorm goal.context
                                                             typ
                                                            in
                                                         {
                                                           context =
                                                             (goal.context);
                                                           witness =
                                                             uu____3377;
                                                           goal_ty =
                                                             uu____3378;
                                                           opts = (goal.opts)
                                                         }))
                                              in
                                           let rec filter' f xs =
                                             match xs with
                                             | [] -> []
                                             | x::xs1 ->
                                                 let uu____3416 = f x xs1  in
                                                 if uu____3416
                                                 then
                                                   let uu____3419 =
                                                     filter' f xs1  in
                                                   x :: uu____3419
                                                 else filter' f xs1
                                              in
                                           let sub_goals1 =
                                             filter'
                                               (fun g1  ->
                                                  fun goals  ->
                                                    let uu____3433 =
                                                      checkone g1.witness
                                                        goals
                                                       in
                                                    Prims.op_Negation
                                                      uu____3433) sub_goals
                                              in
                                           let uu____3434 =
                                             add_irrelevant_goal goal.context
                                               pre goal.opts
                                              in
                                           bind uu____3434
                                             (fun uu____3439  ->
                                                let uu____3440 =
                                                  trytac trivial  in
                                                bind uu____3440
                                                  (fun uu____3449  ->
                                                     let uu____3452 =
                                                       add_implicits
                                                         g.FStar_TypeChecker_Env.implicits
                                                        in
                                                     bind uu____3452
                                                       (fun uu____3456  ->
                                                          add_goals
                                                            sub_goals1))))))))))
  
let rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____3468 =
           FStar_All.pipe_left mlog
             (fun uu____3478  ->
                let uu____3479 =
                  FStar_Syntax_Print.bv_to_string
                    (FStar_Pervasives_Native.fst h)
                   in
                let uu____3480 =
                  FStar_Syntax_Print.term_to_string
                    (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort
                   in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3479
                  uu____3480)
            in
         bind uu____3468
           (fun uu____3492  ->
              let uu____3493 =
                let uu____3496 =
                  let uu____3497 =
                    FStar_TypeChecker_Env.lookup_bv goal.context
                      (FStar_Pervasives_Native.fst h)
                     in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3497
                   in
                FStar_Syntax_Util.destruct_typ_as_formula uu____3496  in
              match uu____3493 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                  (l,uu____3509::(x,uu____3511)::(e,uu____3513)::[])) when
                  FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
                  let uu____3560 =
                    let uu____3561 = FStar_Syntax_Subst.compress x  in
                    uu____3561.FStar_Syntax_Syntax.n  in
                  (match uu____3560 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___101_3568 = goal  in
                         let uu____3569 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.witness
                            in
                         let uu____3572 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty
                            in
                         {
                           context = (uu___101_3568.context);
                           witness = uu____3569;
                           goal_ty = uu____3572;
                           opts = (uu___101_3568.opts)
                         }  in
                       replace_cur goal1
                   | uu____3575 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____3576 -> fail "Not an equality hypothesis"))
  
let clear : Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3584 = FStar_TypeChecker_Env.pop_bv goal.context  in
       match uu____3584 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty  in
           let uu____3606 = FStar_Util.set_mem x fns_ty  in
           if uu____3606
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____3610 = new_uvar env' goal.goal_ty  in
              bind uu____3610
                (fun uu____3625  ->
                   match uu____3625 with
                   | (u,g) ->
                       let uu____3634 =
                         let uu____3635 =
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness u
                            in
                         Prims.op_Negation uu____3635  in
                       if uu____3634
                       then fail "clear: unification failed"
                       else
                         (let new_goal =
                            let uu___102_3640 = goal  in
                            let uu____3641 = bnorm env' u  in
                            {
                              context = env';
                              witness = uu____3641;
                              goal_ty = (uu___102_3640.goal_ty);
                              opts = (uu___102_3640.opts)
                            }  in
                          bind dismiss
                            (fun uu____3643  -> add_goals [new_goal])))))
  
let clear_hd : name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3655 = FStar_TypeChecker_Env.pop_bv goal.context  in
         match uu____3655 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
  
let revert : Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____3682 = FStar_TypeChecker_Env.pop_bv goal.context  in
       match uu____3682 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____3704 = FStar_Syntax_Syntax.mk_Total goal.goal_ty  in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____3704
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___103_3738 = goal  in
              {
                context = env';
                witness = w';
                goal_ty = typ';
                opts = (uu___103_3738.opts)
              }))
  
let revert_hd : name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____3750 = FStar_TypeChecker_Env.pop_bv goal.context  in
         match uu____3750 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____3771 = FStar_Syntax_Print.bv_to_string x  in
               let uu____3772 = FStar_Syntax_Print.bv_to_string y  in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____3771 uu____3772
             else revert)
  
let rec revert_all_hd : name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____3790 = revert_all_hd xs1  in
        bind uu____3790 (fun uu____3794  -> revert_hd x)
  
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
           let uu___104_3811 = g  in
           {
             context = ctx';
             witness = (uu___104_3811.witness);
             goal_ty = (uu___104_3811.goal_ty);
             opts = (uu___104_3811.opts)
           }  in
         bind dismiss (fun uu____3813  -> add_goals [g']))
  
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
           let uu___105_3830 = g  in
           {
             context = ctx';
             witness = (uu___105_3830.witness);
             goal_ty = (uu___105_3830.goal_ty);
             opts = (uu___105_3830.opts)
           }  in
         bind dismiss (fun uu____3832  -> add_goals [g']))
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3874 = f x  in
          bind uu____3874
            (fun y  ->
               let uu____3882 = mapM f xs  in
               bind uu____3882 (fun ys  -> ret (y :: ys)))
  
let rec tac_bottom_fold_env :
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____3928 = FStar_Syntax_Subst.compress t  in
          uu____3928.FStar_Syntax_Syntax.n  in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env  in
              let uu____3963 = ff hd1  in
              bind uu____3963
                (fun hd2  ->
                   let fa uu____3983 =
                     match uu____3983 with
                     | (a,q) ->
                         let uu____3996 = ff a  in
                         bind uu____3996 (fun a1  -> ret (a1, q))
                      in
                   let uu____4009 = mapM fa args  in
                   bind uu____4009
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____4069 = FStar_Syntax_Subst.open_term bs t1  in
              (match uu____4069 with
               | (bs1,t') ->
                   let uu____4078 =
                     let uu____4081 =
                       FStar_TypeChecker_Env.push_binders env bs1  in
                     tac_bottom_fold_env f uu____4081 t'  in
                   bind uu____4078
                     (fun t''  ->
                        let uu____4085 =
                          let uu____4086 =
                            let uu____4103 =
                              FStar_Syntax_Subst.close_binders bs1  in
                            let uu____4104 = FStar_Syntax_Subst.close bs1 t''
                               in
                            (uu____4103, uu____4104, k)  in
                          FStar_Syntax_Syntax.Tm_abs uu____4086  in
                        ret uu____4085))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____4125 -> ret tn  in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___106_4129 = t  in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.pos =
                    (uu___106_4129.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___106_4129.FStar_Syntax_Syntax.vars)
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
            let uu____4158 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____4158 with
            | (t1,lcomp,g) ->
                let uu____4170 =
                  (let uu____4173 = FStar_Syntax_Util.is_total_lcomp lcomp
                      in
                   Prims.op_Negation uu____4173) ||
                    (let uu____4175 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____4175)
                   in
                if uu____4170
                then ret t1
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                   let uu____4182 = new_uvar env typ  in
                   bind uu____4182
                     (fun uu____4198  ->
                        match uu____4198 with
                        | (ut,guard) ->
                            (log ps
                               (fun uu____4211  ->
                                  let uu____4212 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  let uu____4213 =
                                    FStar_Syntax_Print.term_to_string ut  in
                                  FStar_Util.print2
                                    "Pointwise_rec: making equality %s = %s\n"
                                    uu____4212 uu____4213);
                             (let uu____4214 =
                                let uu____4217 =
                                  let uu____4218 =
                                    FStar_TypeChecker_TcTerm.universe_of env
                                      typ
                                     in
                                  FStar_Syntax_Util.mk_eq2 uu____4218 typ t1
                                    ut
                                   in
                                add_irrelevant_goal env uu____4217 opts  in
                              bind uu____4214
                                (fun uu____4221  ->
                                   let uu____4222 =
                                     bind tau
                                       (fun uu____4228  ->
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env guard;
                                          (let ut1 =
                                             FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                               env ut
                                              in
                                           ret ut1))
                                      in
                                   focus uu____4222)))))
  
let pointwise : Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____4250 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals"  in
         match uu____4250 with
         | (g,gs) ->
             let gt1 = g.goal_ty  in
             (log ps
                (fun uu____4287  ->
                   let uu____4288 = FStar_Syntax_Print.term_to_string gt1  in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____4288);
              bind dismiss_all
                (fun uu____4291  ->
                   let uu____4292 =
                     tac_bottom_fold_env (pointwise_rec ps tau g.opts)
                       g.context gt1
                      in
                   bind uu____4292
                     (fun gt'  ->
                        log ps
                          (fun uu____4302  ->
                             let uu____4303 =
                               FStar_Syntax_Print.term_to_string gt'  in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____4303);
                        (let uu____4304 = push_goals gs  in
                         bind uu____4304
                           (fun uu____4308  ->
                              add_goals
                                [(let uu___107_4310 = g  in
                                  {
                                    context = (uu___107_4310.context);
                                    witness = (uu___107_4310.witness);
                                    goal_ty = gt';
                                    opts = (uu___107_4310.opts)
                                  })]))))))
  
let trefl : Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4330 = FStar_Syntax_Util.un_squash g.goal_ty  in
       match uu____4330 with
       | FStar_Pervasives_Native.Some t ->
           let uu____4342 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____4342 with
            | (hd1,args) ->
                let uu____4375 =
                  let uu____4388 =
                    let uu____4389 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____4389.FStar_Syntax_Syntax.n  in
                  (uu____4388, args)  in
                (match uu____4375 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4403::(l,uu____4405)::(r,uu____4407)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____4454 =
                       let uu____4455 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r  in
                       Prims.op_Negation uu____4455  in
                     if uu____4454
                     then
                       let uu____4458 = FStar_Syntax_Print.term_to_string l
                          in
                       let uu____4459 = FStar_Syntax_Print.term_to_string r
                          in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____4458 uu____4459
                     else (solve g FStar_Syntax_Util.exp_unit; dismiss)
                 | (hd2,uu____4463) ->
                     let uu____4480 = FStar_Syntax_Print.term_to_string t  in
                     fail1 "trefl: not an equality (%s)" uu____4480))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let dup : Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____4488 = new_uvar g.context g.goal_ty  in
       bind uu____4488
         (fun uu____4503  ->
            match uu____4503 with
            | (u,u_g) ->
                let g' =
                  let uu___108_4513 = g  in
                  {
                    context = (uu___108_4513.context);
                    witness = u;
                    goal_ty = (uu___108_4513.goal_ty);
                    opts = (uu___108_4513.opts)
                  }  in
                bind dismiss
                  (fun uu____4516  ->
                     let uu____4517 =
                       let uu____4520 =
                         let uu____4521 =
                           FStar_TypeChecker_TcTerm.universe_of g.context
                             g.goal_ty
                            in
                         FStar_Syntax_Util.mk_eq2 uu____4521 g.goal_ty u
                           g.witness
                          in
                       add_irrelevant_goal g.context uu____4520 g.opts  in
                     bind uu____4517
                       (fun uu____4524  ->
                          let uu____4525 = add_goals [g']  in
                          bind uu____4525 (fun uu____4529  -> ret ())))))
  
let flip : Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___109_4546 = ps  in
              {
                main_context = (uu___109_4546.main_context);
                main_goal = (uu___109_4546.main_goal);
                all_implicits = (uu___109_4546.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___109_4546.smt_goals)
              })
       | uu____4547 -> fail "flip: less than 2 goals")
  
let later : Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___110_4562 = ps  in
              {
                main_context = (uu___110_4562.main_context);
                main_goal = (uu___110_4562.main_goal);
                all_implicits = (uu___110_4562.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___110_4562.smt_goals)
              }))
  
let qed : Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____4569 -> fail "Not done!")
  
let cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____4611 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t  in
         match uu____4611 with
         | (t1,typ,guard) ->
             let uu____4627 = FStar_Syntax_Util.head_and_args typ  in
             (match uu____4627 with
              | (hd1,args) ->
                  let uu____4670 =
                    let uu____4683 =
                      let uu____4684 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____4684.FStar_Syntax_Syntax.n  in
                    (uu____4683, args)  in
                  (match uu____4670 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____4703)::(q,uu____4705)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.or_lid
                       ->
                       let v_p =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None p
                          in
                       let v_q =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None q
                          in
                       let g1 =
                         let uu___111_4743 = g  in
                         let uu____4744 =
                           FStar_TypeChecker_Env.push_bv g.context v_p  in
                         {
                           context = uu____4744;
                           witness = (uu___111_4743.witness);
                           goal_ty = (uu___111_4743.goal_ty);
                           opts = (uu___111_4743.opts)
                         }  in
                       let g2 =
                         let uu___112_4746 = g  in
                         let uu____4747 =
                           FStar_TypeChecker_Env.push_bv g.context v_q  in
                         {
                           context = uu____4747;
                           witness = (uu___112_4746.witness);
                           goal_ty = (uu___112_4746.goal_ty);
                           opts = (uu___112_4746.opts)
                         }  in
                       bind dismiss
                         (fun uu____4754  ->
                            let uu____4755 = add_goals [g1; g2]  in
                            bind uu____4755
                              (fun uu____4764  ->
                                 let uu____4765 =
                                   let uu____4770 =
                                     FStar_Syntax_Syntax.bv_to_name v_p  in
                                   let uu____4771 =
                                     FStar_Syntax_Syntax.bv_to_name v_q  in
                                   (uu____4770, uu____4771)  in
                                 ret uu____4765))
                   | uu____4776 ->
                       let uu____4789 = FStar_Syntax_Print.term_to_string typ
                          in
                       fail1 "Not a disjunction: %s" uu____4789)))
  
let set_options : Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____4812 = FStar_Util.smap_copy g.opts  in
          FStar_Options.set uu____4812);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___113_4819 = g  in
                 {
                   context = (uu___113_4819.context);
                   witness = (uu___113_4819.witness);
                   goal_ty = (uu___113_4819.goal_ty);
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
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (proofstate,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____4855 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____4855 with
      | (u,uu____4873,g_u) ->
          let g =
            let uu____4888 = FStar_Options.peek ()  in
            { context = env; witness = u; goal_ty = typ; opts = uu____4888 }
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
  